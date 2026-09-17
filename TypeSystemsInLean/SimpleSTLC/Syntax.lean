namespace STLC

abbrev Index := Nat

-- Locally Namelessを採用
inductive Var where
  | bound : Index → Var
  | free  : String → Var
deriving DecidableEq, Repr

inductive Term where
  | var : Var → Term
  | lam : Term → Term
  | ap  : Term → Term → Term
deriving DecidableEq, Repr

open Term

prefix:90 "#" => fun i => Term.var (Var.bound i)
prefix:90 "$" => fun x => Term.var (Var.free x)
prefix:60 "ƛ " => Term.lam
infixl:70 " □ " => Term.ap

end STLC
