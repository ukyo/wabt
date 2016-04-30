/*
 * Copyright 2016 WebAssembly Community Group participants
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *     http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

#include "wasm-lower-expressions.h"

#include <stdio.h>

#include "wasm-ast.h"

#define CHECK_ALLOC_(cond)                                             \
  do {                                                                 \
    if (!(cond)) {                                                     \
      fprintf(stderr, "%s:%d: allocation failed", __FILE__, __LINE__); \
      return WASM_ERROR;                                               \
    }                                                                  \
  } while (0)

#define CHECK_ALLOC(e) CHECK_ALLOC_(WASM_SUCCEEDED(e))
#define CHECK_ALLOC_NULL(v) CHECK_ALLOC_((v) != NULL)

#define CHECK_RESULT(expr) \
  do {                     \
    if (WASM_FAILED(expr)) \
      return WASM_ERROR;   \
  } while (0)

#define V(rtype, type1, type2, mem_size, code, NAME, text) \
  [code] = WASM_TYPE_##type1,
static WasmType s_opcode_type1[] = {WASM_FOREACH_OPCODE(V)};
#undef V

#define V(rtype, type1, type2, mem_size, code, NAME, text) \
  [code] = WASM_TYPE_##type2,
static WasmType s_opcode_type2[] = {WASM_FOREACH_OPCODE(V)};
#undef V

#define TYPE1(expr_type) s_opcode_type1[expr->expr_type.opcode]
#define TYPE2(expr_type) s_opcode_type2[expr->expr_type.opcode]

#define INVALID_LOCAL_INDEX (-1)

typedef WasmExpr** ExprLink;

typedef struct ExprLinkTypePair {
  ExprLink expr_link;
  WasmType type;
} ExprLinkTypePair;

typedef struct LabelNode {
  const WasmLabel* label;
  WasmType expected_type;
  int local_index;
} LabelNode;
WASM_DEFINE_VECTOR(label_node, LabelNode);

typedef struct Context {
  WasmAllocator* allocator;
  WasmModule* module;
  WasmFunc* current_func;
  LabelNodeVector label_stack;
  int max_depth;

  /* TODO(binji): doc */
  ExprLink stmt_link;
  WasmBool is_toplevel;
  WasmBool in_expr;
  WasmBool must_move;
  WasmExpr* non_sequential_control_flow;
} Context;

static void push_label(Context* ctx,
                       const WasmLabel* label,
                       WasmType expected_type,
                       int local_index) {
  LabelNode node;
  node.label = label;
  node.expected_type = expected_type;
  node.local_index = local_index;
  ctx->max_depth++;
  wasm_append_label_node_value(ctx->allocator, &ctx->label_stack, &node);
}

static void pop_label(Context* ctx) {
  assert(ctx->label_stack.size > 0);
  ctx->max_depth--;
  ctx->label_stack.size--;
}

static LabelNode* find_label_by_name(Context* ctx,
                                     const WasmStringSlice* name) {
  size_t i;
  for (i = ctx->label_stack.size; i > 0; --i) {
    LabelNode* node = &ctx->label_stack.data[i - 1];
    if (wasm_string_slices_are_equal(node->label, name))
      return node;
  }
  assert(!"label must exist");
  return NULL;
}

static LabelNode* find_label_by_var(Context* ctx, const WasmVar* var) {
  if (var->type == WASM_VAR_TYPE_NAME)
    return find_label_by_name(ctx, &var->name);

  assert((size_t)var->index < ctx->label_stack.size);
  return &ctx->label_stack.data[ctx->label_stack.size - 1 - var->index];
}

static WasmResult append_local(Context* ctx, WasmType type, int* out_index) {
  WasmFunc* func = ctx->current_func;
  wasm_append_type_value(ctx->allocator, &func->local_types, &type);
  *out_index = func->local_types.size - 1;
  return WASM_OK;
}

static void splice_before(ExprLink to_link, ExprLink from_link) {
  WasmExpr* expr = *from_link;
  *from_link = expr->next;
  expr->next = *to_link;
  *to_link = expr;
}

static WasmResult replace_with_get_local(Context* ctx,
                                         ExprLink expr_link,
                                         int local_index) {
  splice_before(ctx->stmt_link, expr_link);
  WasmExpr* replacement = wasm_new_get_local_expr(ctx->allocator);
  CHECK_ALLOC_NULL(replacement);
  replacement->get_local.var.index = local_index;
  replacement->next = *expr_link;
  *expr_link = replacement;
  return WASM_OK;
}

static WasmResult wrap_with_set_local(Context* ctx,
                                      ExprLink expr_link,
                                      int local_index) {
  WasmExpr* wrapper = wasm_new_set_local_expr(ctx->allocator);
  CHECK_ALLOC_NULL(wrapper);
  wrapper->set_local.var.index = local_index;
  wrapper->set_local.expr = *expr_link;
  wrapper->next = (*expr_link)->next;
  *expr_link = wrapper;
  return WASM_OK;
}

static WasmResult wrap_with_return(Context* ctx, ExprLink expr_link) {
  WasmExpr* wrapper = wasm_new_return_expr(ctx->allocator);
  CHECK_ALLOC_NULL(wrapper);
  wrapper->return_.expr = *expr_link;
  wrapper->next = (*expr_link)->next;
  *expr_link = wrapper;
  return WASM_OK;
}

static WasmResult visit_expr(Context* ctx,
                             ExprLink expr_link,
                             WasmType expected_type);

static WasmResult visit_statement_list(Context* ctx,
                                       ExprLink first_link,
                                       WasmType expected_type,
                                       int local_index) {
  ExprLink saved_stmt_link = ctx->stmt_link;
  ExprLink expr_link = first_link;
  WasmBool was_toplevel = ctx->is_toplevel;
  WasmBool saved_must_move = ctx->must_move;
  ctx->is_toplevel = WASM_FALSE;
  while (*expr_link) {
    WasmBool is_last_child = (*expr_link)->next == NULL;

    if (is_last_child && expected_type != WASM_TYPE_VOID) {
      if (was_toplevel)
        CHECK_RESULT(wrap_with_return(ctx, expr_link));
      else
        CHECK_RESULT(wrap_with_set_local(ctx, expr_link, local_index));
    }

    ExprLink next_stmt = &(*expr_link)->next;
    ctx->stmt_link = expr_link;
    ctx->must_move = WASM_FALSE;
    ctx->in_expr = WASM_FALSE;
    ctx->non_sequential_control_flow = NULL;
    CHECK_RESULT(visit_expr(ctx, expr_link,
                            is_last_child ? expected_type : WASM_TYPE_VOID));
    if (ctx->non_sequential_control_flow) {
      WasmExpr* dont_remove = *next_stmt;
      WasmExpr* to_remove = ctx->non_sequential_control_flow->next;
      if (to_remove) {
        while (to_remove != dont_remove) {
          WasmExpr* next = to_remove->next;
          wasm_destroy_expr(ctx->allocator, to_remove);
          to_remove = next;
        }
        ctx->non_sequential_control_flow->next = dont_remove;
      }
    }
    expr_link = next_stmt;
  }
  ctx->stmt_link = saved_stmt_link;
  ctx->must_move = saved_must_move;
  return WASM_OK;
}

static WasmResult visit_expr(Context* ctx,
                             ExprLink expr_link,
                             WasmType expected_type) {
  WasmExpr* expr = *expr_link;
  WasmBool is_stmt = WASM_FALSE;
  WasmBool must_move = ctx->must_move;
  WasmBool must_move_children = WASM_FALSE;

  switch (expr->type) {
    case WASM_EXPR_TYPE_BLOCK:
    case WASM_EXPR_TYPE_BR_IF:
    case WASM_EXPR_TYPE_BR_TABLE:
    case WASM_EXPR_TYPE_IF:
    case WASM_EXPR_TYPE_IF_ELSE:
    case WASM_EXPR_TYPE_LOOP:
      is_stmt = WASM_TRUE;
      must_move = WASM_TRUE;
      break;
    case WASM_EXPR_TYPE_SELECT:
      /* select is represented in asm.js as ?:, but the evaluation order is
       * incorrect. Moving the children out of the expression ensures the
       * correct evaluation order. */
      must_move_children = WASM_TRUE;
      break;
    case WASM_EXPR_TYPE_BR:
    case WASM_EXPR_TYPE_RETURN:
    case WASM_EXPR_TYPE_UNREACHABLE:
      is_stmt = WASM_TRUE;
      must_move = WASM_TRUE;
      ctx->non_sequential_control_flow = expr;
      break;
    default:
      break;
  }

  /* first move out anything that must be moved */
  int local_index = INVALID_LOCAL_INDEX;
  if (ctx->in_expr && must_move) {
    if (!ctx->non_sequential_control_flow) {
      CHECK_RESULT(append_local(ctx, expected_type, &local_index));
      if (!is_stmt)
        CHECK_RESULT(wrap_with_set_local(ctx, expr_link, local_index));
    }

    replace_with_get_local(ctx, expr_link, local_index);
    /* if we moved this expression out, none of its descendants need to move
     * out unless they are explicitly required to. This is because child
     * expressions are implicitly evaluated before their parents. */
    ctx->must_move = WASM_FALSE;
  }
  if (must_move_children)
    ctx->must_move = WASM_TRUE;
  ctx->in_expr = WASM_TRUE;

  /* now visit the child expressions in reverse evaulation order */
  switch (expr->type) {
    case WASM_EXPR_TYPE_BINARY:
      CHECK_RESULT(visit_expr(ctx, &expr->binary.right, TYPE2(binary)));
      CHECK_RESULT(visit_expr(ctx, &expr->binary.left, TYPE1(binary)));
      break;

    case WASM_EXPR_TYPE_BLOCK:
      push_label(ctx, &expr->block.label, expected_type, local_index);
      CHECK_RESULT(visit_statement_list(ctx, &expr->block.first, expected_type,
                                        local_index));
      pop_label(ctx);
      break;

    case WASM_EXPR_TYPE_BR:
      if (expr->br.expr) {
        LabelNode* node = find_label_by_var(ctx, &expr->br.var);
        splice_before(ctx->stmt_link, &expr->br.expr);
        ExprLink br_value = ctx->stmt_link;
        CHECK_RESULT(wrap_with_set_local(ctx, br_value, node->local_index));
        CHECK_RESULT(visit_expr(ctx, br_value, node->expected_type));
      }
      break;

    case WASM_EXPR_TYPE_BR_IF:
      CHECK_RESULT(visit_expr(ctx, &expr->br_if.cond, WASM_TYPE_I32));
      if (expr->br_if.expr) {
        LabelNode* node = find_label_by_var(ctx, &expr->br_if.var);
        splice_before(ctx->stmt_link, &expr->br_if.expr);
        ExprLink brif_value = ctx->stmt_link;
        CHECK_RESULT(wrap_with_set_local(ctx, brif_value, node->local_index));
        CHECK_RESULT(visit_expr(ctx, brif_value, node->expected_type));
      }
      break;

    case WASM_EXPR_TYPE_BR_TABLE:
      if (expr->br_table.expr) {
        CHECK_RESULT(visit_expr(ctx, &expr->br_table.expr, WASM_TYPE_I32));
      }
      CHECK_RESULT(visit_expr(ctx, &expr->br_table.key, WASM_TYPE_I32));
      break;

    case WASM_EXPR_TYPE_CALL: {
      WasmFunc* callee = wasm_get_func_by_var(ctx->module, &expr->call.var);
      const WasmFuncSignature* sig =
          wasm_decl_get_signature(ctx->module, &callee->decl);
      ExprLink* arg_links = alloca(sizeof(ExprLink) * expr->call.num_args);
      size_t i;
      ExprLink arg = &expr->call.first_arg;
      for (i = 0; *arg; arg = &(*arg)->next, ++i)
        arg_links[i] = arg;
      for (i = expr->call.num_args; i > 0; --i) {
        CHECK_RESULT(
            visit_expr(ctx, arg_links[i - 1], sig->param_types.data[i - 1]));
      }
      break;
    }

    case WASM_EXPR_TYPE_CALL_IMPORT: {
      WasmImport* import = wasm_get_import_by_var(ctx->module, &expr->call.var);
      const WasmFuncSignature* sig =
          wasm_decl_get_signature(ctx->module, &import->decl);
      ExprLink* arg_links = alloca(sizeof(ExprLink) * expr->call.num_args);
      size_t i;
      ExprLink arg = &expr->call.first_arg;
      for (i = 0; *arg; arg = &(*arg)->next, ++i)
        arg_links[i] = arg;
      for (i = expr->call.num_args; i > 0; --i) {
        CHECK_RESULT(
            visit_expr(ctx, arg_links[i - 1], sig->param_types.data[i - 1]));
      }
      break;
    }

    case WASM_EXPR_TYPE_CALL_INDIRECT: {
      WasmFuncType* func_type =
          wasm_get_func_type_by_var(ctx->module, &expr->call_indirect.var);
      ExprLink* arg_links =
          alloca(sizeof(ExprLink) * expr->call_indirect.num_args);
      size_t i;
      ExprLink arg = &expr->call_indirect.first_arg;
      for (i = 0; *arg; arg = &(*arg)->next, ++i)
        arg_links[i] = arg;
      for (i = expr->call_indirect.num_args; i > 0; --i) {
        CHECK_RESULT(visit_expr(ctx, arg_links[i - 1],
                                func_type->sig.param_types.data[i - 1]));
      }
      CHECK_RESULT(visit_expr(ctx, &expr->call_indirect.expr, WASM_TYPE_I32));
      break;
    }

    case WASM_EXPR_TYPE_COMPARE:
      CHECK_RESULT(visit_expr(ctx, &expr->compare.right, TYPE2(compare)));
      CHECK_RESULT(visit_expr(ctx, &expr->compare.left, TYPE1(compare)));
      break;

    case WASM_EXPR_TYPE_CONVERT:
      CHECK_RESULT(visit_expr(ctx, &expr->convert.expr, TYPE1(convert)));
      break;

    case WASM_EXPR_TYPE_GROW_MEMORY:
      CHECK_RESULT(visit_expr(ctx, &expr->grow_memory.expr, WASM_TYPE_I32));
      break;

    case WASM_EXPR_TYPE_IF:
      push_label(ctx, &expr->if_.true_.label, expected_type, local_index);
      CHECK_RESULT(visit_statement_list(ctx, &expr->if_.true_.first,
                                        expected_type, local_index));
      pop_label(ctx);
      CHECK_RESULT(visit_expr(ctx, &expr->if_.cond, WASM_TYPE_I32));
      break;

    case WASM_EXPR_TYPE_IF_ELSE: {
      push_label(ctx, &expr->if_else.false_.label, expected_type, local_index);
      CHECK_RESULT(visit_statement_list(ctx, &expr->if_else.false_.first,
                                        expected_type, local_index));
      pop_label(ctx);
      push_label(ctx, &expr->if_else.true_.label, expected_type, local_index);
      CHECK_RESULT(visit_statement_list(ctx, &expr->if_else.true_.first,
                                        expected_type, local_index));
      pop_label(ctx);
      CHECK_RESULT(visit_expr(ctx, &expr->if_else.cond, WASM_TYPE_I32));
      break;
    }

    case WASM_EXPR_TYPE_LOAD:
      CHECK_RESULT(visit_expr(ctx, &expr->load.addr, TYPE1(load)));
      break;

    case WASM_EXPR_TYPE_LOOP:
      push_label(ctx, &expr->loop.outer, expected_type, local_index);
      push_label(ctx, &expr->loop.inner, WASM_TYPE_VOID, INVALID_LOCAL_INDEX);
      CHECK_RESULT(visit_statement_list(ctx, &expr->loop.first, expected_type,
                                        local_index));
      pop_label(ctx);
      pop_label(ctx);
      break;

    case WASM_EXPR_TYPE_RETURN:
      if (expr->return_.expr) {
        WasmType result_type =
            wasm_get_result_type(ctx->module, ctx->current_func);
        CHECK_RESULT(visit_expr(ctx, &expr->return_.expr, result_type));
      }
      break;

    case WASM_EXPR_TYPE_SELECT:
      CHECK_RESULT(visit_expr(ctx, &expr->select.cond, WASM_TYPE_I32));
      CHECK_RESULT(visit_expr(ctx, &expr->select.false_, expected_type));
      CHECK_RESULT(visit_expr(ctx, &expr->select.true_, expected_type));
      break;

    case WASM_EXPR_TYPE_SET_LOCAL: {
      WasmType type;
      WasmResult result = wasm_get_local_type_by_var(
          ctx->module, ctx->current_func, &expr->set_local.var, &type);
      WASM_USE(result);
      assert(WASM_SUCCEEDED(result));
      CHECK_RESULT(visit_expr(ctx, &expr->set_local.expr, type));
      break;
    }

    case WASM_EXPR_TYPE_STORE:
      CHECK_RESULT(visit_expr(ctx, &expr->store.value, TYPE2(store)));
      CHECK_RESULT(visit_expr(ctx, &expr->store.addr, TYPE1(store)));
      break;

    case WASM_EXPR_TYPE_UNARY:
      CHECK_RESULT(visit_expr(ctx, &expr->unary.expr, TYPE1(store)));
      break;

    default:
      break;
  }

  /* if this expression was moved (or its children moved), any expressions that
   * precede it in evaluation order must also be moved. */
  if (must_move || must_move_children)
    ctx->must_move = WASM_TRUE;
  return WASM_OK;
}

static WasmResult visit_func(Context* ctx,
                             uint32_t func_index,
                             WasmFunc* func) {
  ctx->current_func = func;
  ctx->is_toplevel = WASM_TRUE;
  WasmType result_type = wasm_get_result_type(ctx->module, func);
  WasmResult result = visit_statement_list(ctx, &func->first_expr, result_type,
                                           INVALID_LOCAL_INDEX);
  ctx->current_func = NULL;
  return result;
}

static WasmResult visit_module(Context* ctx, WasmModule* module) {
  size_t i;
  for (i = 0; i < module->funcs.size; ++i)
    CHECK_RESULT(visit_func(ctx, i, module->funcs.data[i]));
  return WASM_OK;
}

WasmResult wasm_lower_expressions(struct WasmAllocator* allocator,
                                  struct WasmModule* module) {
  Context ctx;
  WASM_ZERO_MEMORY(ctx);
  ctx.allocator = allocator;
  ctx.module = module;
  return visit_module(&ctx, module);
}
