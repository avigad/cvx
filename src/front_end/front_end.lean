import analysis.convex data.matrix data.fin tactic.norm_num

def vec (n : ℕ) := fin n → ℝ

namespace cvx

inductive opt_type
| minimize | maximize

def prob_data : nat → Type
| 0     := ℝ × Prop
| (n+1) := ℝ → prob_data n

def fun_type : nat → Type
| 0 := ℝ
| (n+1) := ℝ → fun_type n

def pred_type : nat → Type
| 0     := Prop
| (n+1) := ℝ → pred_type n

structure cvx_problem :=
(type : opt_type)
(n : nat)
(data : prob_data n)

/-
def is_mimimum (p : cvx_problem) (ε : ℝ) (x : vec (p.n)) :=
p.const x ∧ ∀ y, p.const y → p.obj y ≥ p.obj x - ε

def is_maximum (p : cvx_problem) (ε : ℝ) (x : vec (p.n)) :=
p.const x ∧ ∀ y, p.const y → p.obj y ≤  p.obj x + ε
-/


end cvx
