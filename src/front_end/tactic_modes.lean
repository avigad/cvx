import init.meta.interactive .front_end

open lean
open lean.parser
open tactic
open cvx

-- adapted from tests/interactive/my_tactic_class.lean

meta structure cvx_data :=
(opt : opt_type) (constr : list expr) (status : format)

meta def start_data : cvx_data :=
{ opt := opt_type.minimize, constr := [], status := "" }

meta def cvx_spec :=
state_t cvx_data tactic

meta def prob_type_expr : nat → expr
| 0     := `(real × Prop)
| (n+1) := expr.imp `(real) (prob_type_expr n)

section
local attribute [reducible] cvx_spec
meta instance : monad cvx_spec := by apply_instance
meta instance : monad_state cvx_data cvx_spec := by apply_instance
meta instance : has_monad_lift tactic cvx_spec := by apply_instance
meta instance : has_orelse cvx_spec := by apply_instance
end

meta instance (α : Type) : has_coe (tactic α) (cvx_spec α) :=
⟨monad_lift⟩

namespace cvx_spec

meta def step {α : Type} (t : cvx_spec α) : cvx_spec unit :=
t >> return ()

meta def istep {α : Type} (line0 col0 line col : nat) (t : cvx_spec α) : cvx_spec unit :=
⟨λ v s, result.cases_on (@scope_trace _ line col (λ_, t.run v s))
  (λ ⟨a, v⟩ new_s, result.success ((), v) new_s)
  (λ opt_msg_thunk e new_s, match opt_msg_thunk with
    | some msg_thunk :=
      let msg := λ _ : unit, msg_thunk () ++ format.line ++ v.status
        in
          interaction_monad.result.exception (some msg) (some ⟨line, col⟩) new_s
    | none := interaction_monad.silent_fail new_s
    end)⟩

meta def execute (tac : cvx_spec unit) : tactic unit :=
tac.run start_data >> return ()

meta def save_info (p : pos) : cvx_spec unit :=
do v ← get,
   s ← tactic.read,
   let fmt := v.status, --show_goals,
   tactic.save_info_thunk p
     (λ _, fmt)

namespace interactive
open interactive interactive.types expr
local postfix `?`:9001 := optional
local postfix *:9001 := many

meta def intro_lst : list name → cvx_spec unit
| [] := skip
| (n :: ns) := intro_core n >> intro_lst ns

meta def minimize : cvx_spec unit :=
do s ← get,
   put {opt := opt_type.minimize, status := "cvx problem: minimize" ++ format.line, ..s}

meta def maximize : cvx_spec unit :=
do s ← get,
   put {opt := opt_type.maximize, status := "cvx problem: maximize" ++ format.line, ..s}

meta def vars (varlist : parse ident*): cvx_spec unit :=
do let n := varlist.length,
   let en := reflected.to_expr `(n),
   s ← get,
   e ← match s.opt with
       | opt_type.minimize :=
         tactic.to_expr ``(cvx.cvx_problem.mk cvx.opt_type.minimize %%en)
       | opt_type.maximize :=
         tactic.to_expr ``(cvx.cvx_problem.mk cvx.opt_type.minimize %%en)
   end,
   apply e,
   intro_lst varlist,
   put {status := s.status ++ "variables: " ++ varlist.to_format ++ format.line, ..s},
   return ()

meta def objective (obj : parse texpr) : cvx_spec unit :=
do e ← to_expr obj,
   split,
   exact e,
   s ← get,
   ppe ← pp e,
   put {status := s.status ++ "objective: " ++ ppe ++ format.line ++ "subject to: " ++
        format.line, ..s}

meta def constr (cns : parse texpr) : cvx_spec unit :=
do e ← to_expr cns,
   t ← infer_type e,
   s ← get,
   unify t `(Prop) >> put { constr := e :: s.constr, ..s} <|> fail "constraint must be an assertion",
   ppe ← pp e,
   put {status := s.status ++ " " ++ ppe ++ format.line, constr := e :: s.constr, ..s}

meta def mk_conj : list expr → expr
| []        := `(true)
| [e]       := e
| (e :: es) := `(and %%e %%(mk_conj es))

meta def done : cvx_spec unit :=
do s ← get,
   exact $ mk_conj (s.constr.reverse)

end interactive

end cvx_spec


noncomputable theory
open cvx

--set_option pp.all true

def foo : cvx_problem :=
begin [cvx_spec]
  minimize,
  vars a b c,
  objective (a + 2 * b + c),
  constr a < b,
  constr b^2 < 5,
  constr a + b + c < 17,
  done
end

#print foo
