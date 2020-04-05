-- vim: ts=2 sw=0 sts=-1 et ai tw=70

import ..mynat.lt
import .equinumerous


-- Definitions and theorems relating to finite sets

namespace hidden

universes u

variable {α : Type u}

open myset
open mynat

-- Exclude the actual value so there are m elements
def zero_to (m : mynat) : myset mynat := λ n, n < m

theorem emp_zero_to_zero : empty (zero_to 0) :=
begin
  intro m,
  assume hm,
  from lt_nzero hm,
end

def of_size {α : Type u} (s : myset α) (m : mynat) : Prop :=
equinumerous s (zero_to m)
def finite {α : Type u} (s : myset α) : Prop :=
∃ m : mynat, of_size s m
def infinite {α : Type u} (s : myset α) : Prop := ¬finite s

-- function swapping two naturals. Turns out this is harder
-- to define than I thought
def swap_naturals (a b x: mynat): mynat :=
sorry

-- pigeonhole principle, basically
-- have I overthought this?
-- and can this be done without classical? probably..
theorem no_injection_from_zero_to_succ
(n: mynat) (f: mynat → mynat)
(hwf: well_defined (zero_to (n + 1)) (zero_to n) f):
¬injective hwf :=
begin
  assume h,
  revert f,
  induction n with n hn, {
    intro f, assume hwf,
    exfalso, revert hwf,
    apply @no_wdefined_func_nemp_to_emp
            _ _ (zero_to 1) (zero_to 0) f, {
      assume h,
      have : (0 : mynat) ∈ zero_to 1, {
        from zero_lt_one,
      },
      from h 0 this,
    }, {
      from emp_zero_to_zero,
    },
  }, {
    -- we are trying to show that if
    -- f: {0, ..., n + 1} → {0, ...,  n}
    -- is well-defined then it is not injective.
    -- Consider the pre-image of n. By injectivity, this at most one
    -- number. If it's empty, skip to the restriction.
    -- If not, call it x. Define f': {0, ..., n + 1} → {0, ..., n}
    -- by composing f with the function swapping n + 1 and x. This
    -- function is still injective and has n + 1 ↦ n, so we can
    -- restrict it to {0, ..., n} and its range will restrict to
    -- {0, ..., n - 1}. Then we are done by induction.
    let s: myset mynat := sorry,
    sorry,
  },
end

theorem equinum_zero_to_iff_eq {m n : mynat} :
equinumerous (zero_to m) (zero_to n) → m = n := sorry

-- A set cannot have two different natural sizes
theorem unique_size {α : Type u} (s : myset α) (m n : mynat) :
of_size s m → of_size s n → m = n :=
begin
  assume hm hn,
  unfold of_size at hm hn,
  have hm₂ := equinumerous_symm _ _ hm,
  have h := equinumerous_trans _ _ _ hm₂ hn,
  from equinum_zero_to_iff_eq h,
end

theorem naturals_infinite: infinite (all_of mynat) :=
begin
  assume hfinite,
  cases hfinite with n hn,
  cases hn with f hf,
  cases hf with hwf h,
  sorry,
end

theorem inf_iff_powerset_inf (s : myset α):
infinite s ↔ infinite (power_set s) :=
begin
  split; assume hinf, {
    sorry,
  }, {
    sorry,
  },
end

end hidden
