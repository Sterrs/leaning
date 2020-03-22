import naturals.mynat
import naturals.le

namespace hidden

open mynat

-- proof of the princple of strong induction
-- conceptually quite nice: works by showing that for any N, the statement will
-- hold for all M less than or equal to that N.
theorem strong_induction
(statement: mynat → Prop)
(base_case: statement 0)
(inductive_step: ∀ n: mynat, (∀ m: mynat, m ≤ n → statement m) → statement (succ n)):
∀ k: mynat, statement k :=
begin
    intro k,
    have h_aux: ∀ N: mynat, (∀ M: mynat, M ≤ N → statement M),
    intro N,
    induction N,
    simp,
    intro M,
    assume hMl0,
    have hM0 := le_zero _ hMl0,
    rw hM0,
    from base_case,
    intro M,
    assume hMlesN,
    cases hMlesN with d hd,
    cases d,
    simp at hd,
    rw ←hd,
    from inductive_step N_n N_ih,
    have hMleN: M ≤ N_n,
    existsi d,
    simp at hd,
    from hd,
    from N_ih M hMleN,
    from h_aux (succ k) k (le_to_add k 1),
end

end hidden
