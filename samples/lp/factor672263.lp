\ toysolver: NG
\ toysat: OK
\ scip-2.1.1.darwin.x86_64.gnu.opt.spx.nozimpl: OK
Minimize
 obj: P
Subject To
 [ P * Q ] = 672263 \ = 547*1229
Bounds
 2 <= P <= 819      \ = sqrt 672263
 2 <= Q <= 336131   \ = 672263/2
General
 P Q
End
