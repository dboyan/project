(lambda x:[1,5]. + x 2) 1;
lambda y:[4,7][10,13]. - y 3;
(lambda x:[20,40]. if > x 30 then + x 10 else - x 10) 35;
(lambda x:[20,40]. if < x 30 then 10 else 50) 25;
lambda x:[0,65535].lambda y:[0,65535]. +? x y;
lambda x:[0,65535].lambda y:[0,65535]. try -? x y with 0;
(fix (lambda f:[0,300]->[0,65535]. lambda x:[0,300]. if iszero x then 0 else +? x (f (cast [0,300] (- x 1))))) 100;
(lambda x:[0,100]. lambda y:[0,100]. cast [0,100] + x y) 50 50;
lambda x:[0,65535].lambda y:[0,65535]. + x y;
