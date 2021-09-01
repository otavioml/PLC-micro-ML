(* New test cases for part 2 of the project*)

Prim2 ("*",Prim2 ("*",ConI 17,ConI 2),ConI 2)

Prim2 ("<",ConI 10,ConI 20)

Prim1 ("!",Prim2 ("<",ConI 20,ConI 10))

List [ConI 10,ConI 20,ConI 135,List [ConB true,ConB false]]

Let
    ("f",
     Anon
       (ListT [IntT,IntT,IntT],"$list",
        Let
          ("x",Item (1,Var "$list"),
           Let
             ("y",Item (2,Var "$list"),
              Let
                ("z",Item (3,Var "$list"),
                 Prim2 ("-",Var "x",Prim2 ("*",Var "y",Var "z")))))),
     Call (Var "f",List [ConI 5,ConI 4,ConI 2]))


  Let
    ("E",ESeq (SeqT IntT),
     Let
       ("reverse",
        Anon
          (SeqT IntT,"s",
           Letrec
             ("rev",ListT [SeqT IntT,SeqT IntT],"$list",SeqT IntT,
              Let
                ("s1",Item (1,Var "$list"),
                 Let
                   ("s2",Item (2,Var "$list"),
                    Match
                      (Var "s1",
                       [(SOME (Var "E"),Var "s2"),
                        (NONE,
                         Let
                           ("h",Prim1 ("hd",Var "s1"),
                            Let
                              ("t",Prim1 ("tl",Var "s1"),
                               Call
                                 (Var "rev",
                                  List [Var "t",Prim2 ("::",Var "h",Var "s2")]))))]))),
              Call (Var "rev",List [Var "s",Var "E"]))),
        Call
          (Var "reverse",
           Prim2 ("::",ConI 1,Prim2 ("::",ConI 2,Prim2 ("::",ConI 3,Var "E"))))))

(* Factorial Function *)

Letrec
    ("fact",IntT,"x",IntT,
     If
       (Prim2 ("=",Var "x",ConI 1),ConI 1,
        Prim2 ("*",Var "x",Call (Var "fact",Prim2 ("-",Var "x",ConI 1)))),
     Call (Var "fact",ConI 5))

(* Square function *)

Letrec
    ("square",IntT,"x",IntT,Prim2 ("*",Var "x",Var "x"),
     Call (Var "square",ConI 5))

