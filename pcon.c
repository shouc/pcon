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
#define HAVE_PCON 1
#if HAVE_PCON

zval *get_zval(zend_execute_data *zdata, int node_type, const znode_op *node)
{
    zend_free_op should_free;
    zval* r = zend_get_zval_ptr(zdata->opline, node_type, node, zdata, &should_free, BP_VAR_IS);
    return r;
}

static int conc_collect(zend_execute_data *execute_data)
{
    zval* op1 = get_zval(execute_data, execute_data->opline->op1_type, &execute_data->opline->op1);
    zval* op2 = get_zval(execute_data, execute_data->opline->op2_type, &execute_data->opline->op2);

    php_printf("lo: %d\n", execute_data->opline->lineno);
    php_printf("op1_type: %d\n", execute_data->opline->op1_type);
    php_printf("op1: %d\n", op1->value);
    php_printf("op2_type: %d\n", execute_data->opline->op2_type);
    php_printf("op2: %d\n", Z_TYPE_P(op2) == IS_LONG);
    php_printf("op2: %d\n", execute_data->symbol_table);
//    php_printf("op_type: %d\n", execute_data->opline->op1_type);
//    php_printf("lo: %d\n", execute_data->opline->lineno);
//    php_printf("op_type: %d\n", execute_data->opline->op1_type);
    return ZEND_USER_OPCODE_DISPATCH;
}

PHP_MINIT_FUNCTION(pcon)
{
    zend_set_user_opcode_handler(ZEND_IS_EQUAL, conc_collect);
    zend_set_user_opcode_handler(ZEND_ADD, conc_collect);
    zend_set_user_opcode_handler(ZEND_ASSIGN, conc_collect);
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
    NULL,
    NULL,
    NULL,
    NULL,
    PHP_PCON_VERSION,
    STANDARD_MODULE_PROPERTIES
};

#ifdef COMPILE_DL_PCON
ZEND_GET_MODULE(pcon)
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
