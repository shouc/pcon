# PCON
PHP7 extension for concolic execution


### Install
Assume you are using Linux and you have php7.x-dev installed on system.
```
phpize && ./configure
make && make install
```


### TODO
* Add handler for other comparison & assign opcode
* Link ABC and Z3


### Example
```php
<?php
$a = $argv; // uninterpreted variable
$b = true;
echo $b == $a; // type juggling
```

would yield SMT-LIBv2 file
```
(declare-const v0x7f52fba5c008 Int);L2
(assert (!= v0x7f52fba5c008 0));L4
```
