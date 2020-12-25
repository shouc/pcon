dnl $Id$
dnl config.m4 for extension pcon

sinclude(./autoconf/pecl.m4)
sinclude(./autoconf/php-executable.m4)

PECL_INIT([pcon])

PHP_ARG_ENABLE(pcon, whether to enable pcon, [ --enable-pcon   Enable pcon])

if test "$PHP_pcon" != "no"; then
  AC_DEFINE(HAVE_PCON, 1, [whether pcon is enabled])
  PHP_NEW_EXTENSION(pcon, pcon.c, $ext_shared)

  PHP_ADD_MAKEFILE_FRAGMENT
  PHP_INSTALL_HEADERS([ext/pcon], [php_pcon.h])
fi
