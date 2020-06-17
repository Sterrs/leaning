import .basic

namespace hidden
namespace quotint

open mynat
open quotint

variables {m n k : quotint}
variables {a b c : mynat}

@[simp]
theorem coe_succ: (↑(succ a): quotint) = ↑a + 1 := rfl

@[simp] theorem nat_nat_add: (↑a: quotint) + ↑b = ↑(a + b) := rfl

theorem sub_add_neg: m - n = m + (-n) := rfl

theorem add_comm: m + n = n + m :=
begin
  cases quotient.exists_rep m with a ha, subst ha,
  cases quotient.exists_rep n with b hb, subst hb,
  repeat {rw add_eq_cls rfl rfl},
  -- honestly this just happened to work
  apply congr rfl,
  rw int_pair.eq_iff_split,
  simp,
  split; ac_refl,
end

instance add_is_comm: is_commutative quotint add :=
⟨assume a b, add_comm⟩

@[simp]
theorem zero_add: 0 + m = m :=
begin
  cases quotient.exists_rep m with a ha, subst ha,
  rw int_zero,
  rw add_eq_cls rfl rfl,
  apply congr rfl,
  rw int_pair.eq_iff_split,
  simp,
end

@[simp]
theorem add_zero: m + 0 = m :=
begin
  have := @zero_add m,
  rwa add_comm,
end

theorem add_assoc: m + n + k = m + (n + k) :=
begin
  cases quotient.exists_rep m with a ha, subst ha,
  cases quotient.exists_rep n with b hb, subst hb,
  cases quotient.exists_rep k with c hc, subst hc,
  repeat {rw add_eq_cls rfl rfl},
  apply congr rfl,
  rw int_pair.eq_iff_split,
  simp,
  split; ac_refl,
end

instance add_is_assoc: is_associative quotint add :=
⟨assume a b c, add_assoc⟩

@[simp]
theorem neg_distr: -(m + n) = -m + -n :=
begin
  cases quotient.exists_rep m with a ha, subst ha,
  cases quotient.exists_rep n with b hb, subst hb,
  repeat {rw add_eq_cls rfl rfl <|> rw neg_eq_cls rfl},
  apply congr rfl,
  rw int_pair.eq_iff_split,
  simp,
end

private lemma add_cancel_mp (k: quotint): m + k = n + k → m = n :=
begin
  assume hmknk,
  cases quotient.exists_rep m with a ha, subst ha,
  cases quotient.exists_rep n with b hb, subst hb,
  cases quotient.exists_rep k with c hc, subst hc,
  repeat {rw add_eq_cls rfl rfl at hmknk},
  have := quotient.exact hmknk,
  rw int_pair.setoid_equiv at this,
  simp at this,
  apply quotient.sound,
  rw int_pair.setoid_equiv,
  apply @mynat.add_cancel _ _ (c.a + c.b),
  transitivity (a.a + c.a + (b.b + c.b)), {
    -- oh dear. It seems ac_refl needed a nudge
    rw mynat.add_comm,
    ac_refl,
  }, {
    rw this,
    ac_refl,
  },
end

-- It's more useful as an iff
@[simp]
theorem add_cancel (k : quotint): m + k = n + k ↔ m = n :=
⟨add_cancel_mp k, assume h, by congr; assumption⟩

@[simp]
theorem add_cancel_to_zero: n + m = m ↔ n = 0 :=
by rw [←@zero_add m, ←add_assoc, add_cancel, add_zero]

@[simp]
theorem self_neg_add: m + (-m) = 0 :=
begin
  cases quotient.exists_rep m with a ha, subst ha,
  rw int_zero,
  rw neg_eq_cls rfl,
  rw add_eq_cls rfl rfl,
  apply quotient.sound,
  rw int_pair.setoid_equiv,
  simp,
  rw mynat.add_comm,
end

@[simp]
theorem neg_self_add : -m + m = 0 := by
rw add_comm; apply self_neg_add

end quotint
end hidden
