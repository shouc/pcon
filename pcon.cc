/*
  +----------------------------------------------------------------------+
  | Skeleton PHP extension                                               |
  +----------------------------------------------------------------------+
  | Copyright (c) 2018 NAME                                              |
  +----------------------------------------------------------------------+
  | Permission is hereby granted, free of charge, to any person          |
  | obtaining a copy of this software and associated documentation files |
  | (the "Software"), to deal in the Software without restriction,       |
  | including without limitation the rights to use, copy, modify, merge, |
  | publish, distribute, sublicense, and/or sell copies of the Software, |
  | and to permit persons to whom the Software is furnished to do so,    |
  | subject to the following conditions:                                 |
  |                                                                      |
  | The above copyright notice and this permission notice shall be       |
  | included in all copies or substantial portions of the Software.      |
  |                                                                      |
  | THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND,      |
  | EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF   |
  | MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND                |
  | NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS  |
  | BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN AN   |
  | ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN    |
  | CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE     |
  | SOFTWARE.                                                            |
  +----------------------------------------------------------------------+
  | Author: NAME <EMAIL@EXAMPLE.COM>                                     |
  +----------------------------------------------------------------------+
*/

#ifdef HAVE_CONFIG_H
# include "config.h"
#endif

#include "php.h"
#include "php_ini.h"
#include "php_pcon.h"
#include "zend_exceptions.h"
#include "ext/standard/info.h"
#include "z3++.h"
#include <map>

#define HAVE_PCON 1
#if HAVE_PCON

zval *get_zval(zend_execute_data *zdata, int node_type, const znode_op *node)
{
    zend_free_op should_free;
    zval* r = zend_get_zval_ptr(zdata->opline, node_type, node, zdata, &should_free, BP_VAR_IS);
    return r;
}
void force_ref(zval *val) {
    if (!Z_ISREF_P(val) &&
        (Z_TYPE_P(val) != IS_INDIRECT) &&
        (Z_TYPE_P(val) != IS_CONST) &&
        (Z_TYPE_P(val) != IS_CONSTANT_AST))
    {
        if (Z_TYPE_P(val) == IS_UNDEF) {
            ZVAL_NEW_EMPTY_REF(val);
            Z_SET_REFCOUNT_P(val, 2);
            ZVAL_NULL(Z_REFVAL_P(val));
        }
        else {
            ZVAL_MAKE_REF(val);
        }
    }
}

z3::context c;
z3::solver s(c);
struct poly_z3_expr {

    z3::expr str;
    z3::expr bv;
    z3::expr num;
    z3::expr boolv;
};

#define init_poly_z3_expr(variable_name, z3_name)\
    poly_z3_expr variable_name = {\
        c.string_val(""),\
        c.bv_const(z3_name, 256),\
        c.real_const(z3_name),\
        c.bool_const(z3_name)\
    };

std::map<void*, void*> ref_to_ref;
std::map<void*, zval*> ref_to_res;
std::map<void*, poly_z3_expr> ref_to_expr;



#define insert_or_assign_cc17(map, offset, nval) \
    if (map.find(offset) == map.end())\
        map.emplace(offset, nval);\
    else\
        map[offset] = nval;


#define handle_zval(op, zv, expr) \

inline void retrieve_ref_by_zv(void* ref, zval*& res){
    if (ref_to_res.find(ref) == ref_to_res.end()){
        if (ref_to_ref.find(ref) == ref_to_ref.end())
            res = nullptr;
        else
            retrieve_ref_by_zv(ref_to_ref[ref], res);
    }
    else
        res =  ref_to_res[ref];
}

void retrieve_ref_by_expr(void* ref, poly_z3_expr& expr){
    if (ref_to_expr.find(ref) == ref_to_expr.end()){
        if (ref_to_ref.find(ref) == ref_to_ref.end()) {
            std::ostringstream z3_name;
            z3_name << ref;
            init_poly_z3_expr(new_z3_expr, z3_name.str().c_str())
            ref_to_expr[ref] = new_z3_expr;
            expr = new_z3_expr;
        }
        else
            retrieve_ref_by_expr(ref_to_ref[ref], expr);
    }
    else
        expr = ref_to_expr[ref];
}

void handle_assign(zend_execute_data* execute_data,
                   zval* op1,
                   zval* op2,
                   z3::expr& expr,
                   unsigned int& T){
    php_printf("x");
    switch (Z_TYPE_P(op1)) {
        case IS_NULL:
        case IS_UNDEF:
            force_ref(op1);
            handle_assign(execute_data, op1, op2, expr, T);
            return;
        case IS_REFERENCE:
            switch (Z_TYPE_P(op2)) {
                case IS_RESOURCE:
                case IS_OBJECT:
                case IS_ARRAY:
                    php_printf("UNKNOWN OP: Unsupported type %d\n", Z_TYPE_P(op2));
                    break;
                case IS_REFERENCE:
                    insert_or_assign_cc17(ref_to_ref, Z_REFVAL_P(op1), Z_REFVAL_P(op2))
                    break;
                case IS_LONG:
                case IS_DOUBLE:
                case IS_TRUE:
                case IS_FALSE:
                case IS_STRING:
                    insert_or_assign_cc17(ref_to_res, Z_REFVAL_P(op1), op2)
                    break;
                default:
                    php_printf("UNKNOWN OP: Assign by type %d\n", Z_TYPE_P(op2));
                    break;
            }
            break;
        default:
            php_printf("UNKNOWN OP: Assign to type %d\n", Z_TYPE_P(op1));
            break;
    }
}

void handle_equal(zend_execute_data* execute_data,
                   zval* op1,
                   zval* op2,
                   z3::expr& expr,
                   unsigned int& T){
    php_printf("x");
    switch (Z_TYPE_P(op1)) {
        case IS_NULL:
        case IS_UNDEF:
            php_printf("Ignoring undefined comparison");
            return;
        case IS_RESOURCE:
        case IS_OBJECT:
        case IS_ARRAY:
            php_printf("UNKNOWN OP: Unsupported type %d\n", Z_TYPE_P(op1));
            break;
        case IS_REFERENCE:
            zval* op1_res;
            retrieve_ref_by_zv(Z_REFVAL_P(op1), op1_res);
            if (op1_res != nullptr){
                if (Z_TYPE_P(op2) == IS_REFERENCE){
                    zval* op2_res;
                    retrieve_ref_by_zv(Z_REFVAL_P(op1), op2_res);
                    if (op2_res != nullptr)
                        goto rv_comparison_die;
                    init_poly_z3_expr(op2_expr, "x")
                    retrieve_ref_by_expr(Z_REFVAL_P(op2), op2_expr);
                    switch (Z_TYPE_P(op1_res)) {
                        case IS_LONG:
                            s.add((double) Z_LVAL_P(op1_res) == op2_expr.num);
                            break;
                        case IS_DOUBLE:
                            s.add(Z_DVAL_P(op1_res) == op2_expr.num);
                            break;
                        case IS_TRUE:
                            s.add(true == op2_expr.boolv);
                            break;
                        case IS_FALSE:
                            s.add(false == op2_expr.boolv);
                            break;
                        case IS_STRING:
                            s.add(false == op2_expr.boolv);
                            break;

                    }
                    s.add(op1_res == op2_expr);
                } else if (Z_TYPE_P(op2) == IS_REFERENCE){

                }
rv_comparison_die:
                // we don't care about rv comparison (e.g. 1==1)
                php_printf("Ignoring real value comparison");
                return;
            } else {
                init_poly_z3_expr(op1_expr, "x")
                retrieve_ref_by_expr(Z_REFVAL_P(op1), op1_expr);

            }
            break;
        default:
            php_printf("UNKNOWN OP: Assign to type %d\n", Z_TYPE_P(op1));
            break;
    }
}


static int conc_collect(zend_execute_data *execute_data)
{
    zval* op1 = get_zval(execute_data, execute_data->opline->op1_type, &execute_data->opline->op1);
    zval* op2 = get_zval(execute_data, execute_data->opline->op2_type, &execute_data->opline->op2);
    php_printf("================= lo: %d =================\n", execute_data->opline->lineno);

    z3::expr sym(c);
    unsigned int callback_code;
    switch (execute_data->opline->opcode) {
        case ZEND_ASSIGN:
            handle_assign(execute_data, op1, op2, sym, callback_code);
            break;
        case ZEND_IS_EQUAL:
            handle_equal(execute_data, op1, op2, sym, callback_code);
            break;
    }

    return ZEND_USER_OPCODE_DISPATCH;
}


PHP_MINIT_FUNCTION(pcon)
{
    z3::expr x = c.bv_const("x", 32);
    z3::expr y = c.bv_const("y", 32);
    s.add(x > 2);
    s.add(x + y < 5);
    zend_set_user_opcode_handler(ZEND_IS_EQUAL, conc_collect);
    zend_set_user_opcode_handler(ZEND_ADD, conc_collect);
    zend_set_user_opcode_handler(ZEND_ASSIGN, conc_collect);
    return SUCCESS;
}

PHP_MSHUTDOWN_FUNCTION(pcon)
{
//    Z3_del_context(ctx);
    return SUCCESS;
}


/* Argument info for each function, used for reflection */
ZEND_BEGIN_ARG_INFO_EX(arginfo_pcon_nop, 0, 1, 0)
    ZEND_ARG_TYPE_INFO(0, str, IS_STRING, 1)
ZEND_END_ARG_INFO()

/* Add all functions. (Keep PHP_FE_END as last element) */
static const zend_function_entry functions[] = {
    PHP_FE(pcon_nop, arginfo_pcon_nop)
    PHP_FE_END
};

zend_module_entry pcon_module_entry = {
    STANDARD_MODULE_HEADER,
    PHP_PCON_EXTNAME,
    functions,
    PHP_MINIT(pcon),
    PHP_MSHUTDOWN(pcon),
    NULL,
    NULL,
    NULL,
    PHP_PCON_VERSION,
    STANDARD_MODULE_PROPERTIES
};

#ifdef COMPILE_DL_PCON
extern "C" {
    ZEND_GET_MODULE(pcon)
}
#endif

/* Replace the example function with something better :) */
PHP_FUNCTION(pcon_nop)
{
    zend_string *str;
    ZEND_PARSE_PARAMETERS_START_EX(ZEND_PARSE_PARAMS_THROW, 1, 1)
        Z_PARAM_STR(str)
    ZEND_PARSE_PARAMETERS_END();
    php_printf("2\n");

    RETVAL_STR(str);
}


#endif
