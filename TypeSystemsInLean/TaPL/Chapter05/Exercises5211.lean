-- 型なしラムダ計算の定義
inductive Term where
  | var : String -> Term
  | abs : String -> Term -> Term
  | app : Term -> Term -> Term

open Term

-- 基本コンビネータの定義
def lam := abs
def apply := app

-- Church数と基本演算
def c0 := lam "s" (lam "z" (var "z"))
def c1 := lam "s" (lam "z" (apply (var "s") (var "z")))
def scc := lam "n" (lam "s" (lam "z" (apply (var "s") (apply (apply (var "n") (var "s")) (var "z")))))
def plus := lam "m" (lam "n" (lam "s" (lam "z" (apply (apply (var "m") (var "s")) (apply (apply (var "n") (var "s")) (var "z"))))))
def mult := lam "m" (lam "n" (lam "s" (apply (var "m") (apply (var "n") (var "s")))))
def iszro := lam "n" (apply (apply (var "n") (lam "x" (var "fls"))) (var "tru"))
  where tru := lam "t" (lam "f" (var "t"))
        fls := lam "t" (lam "f" (var "f"))
def prd := lam "n" (lam "s" (lam "z" (apply (apply (apply (var "n") (lam "g" (lam "h" (apply (var "h") (apply (var "g") (var "s")))))) (lam "u" (var "z"))) (lam "u" (var "u")))))

-- 演習5.2.9: test (Church bool) を使った factorial
def test := lam "p" (lam "a" (lam "b" (apply (apply (var "p") (var "a")) (var "b"))))
def fix := lam "f" (apply (lam "x" (apply (var "f") (apply (var "x") (var "x")))) (lam "x" (apply (var "f") (apply (var "x") (var "x")))))

def factorial_with_test :=
  apply fix (lam "fct" (lam "n"
    (apply (apply (apply test (apply iszro (var "n"))) c1)
           (apply (apply mult (var "n"))
                  (apply (var "fct") (apply prd (var "n")))))))

-- 演習5.2.10: churchnat (Nat -> Term 変換)
def churchnat : Nat -> Term
  | 0     => c0
  | n + 1 => apply scc (churchnat n)

-- 演習5.2.11: リストの総和
-- リストの定義: [h, t] = λc. λn. c h (t c n)
-- sumlist = λl. l (λh. λt. plus h t) c0
def sumlist :=
  lam "l" (apply (apply (var "l") (lam "h" (lam "t" (apply (apply plus (var "h")) (var "t"))))) c0)

-- 使用例: リスト [c1, c2] の総和は c3 になるはず
-- sumlist (apply (apply cons c1) (apply (apply cons c2) nil))