-- vim: ts=2 sw=0 sts=-1 et ai tw=70

import ..mynat.lt
import .equinumerous
import ..mylist.map

-- Definitions and theorems relating to finite sets

namespace hidden
namespace myset

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

def of_size (s : myset α) (m : mynat) : Prop :=
equinumerous s (zero_to m)
def finite (s : myset α) : Prop :=
∃ m : mynat, of_size s m
def infinite (s : myset α) : Prop := ¬finite s

theorem zero_to_le_subset (m n: mynat) (h: m ≤ n):
(zero_to m) ⊆ (zero_to n) :=
(λ k h', @lt_le_chain k n m h' h)

-- function swapping two naturals. Useful in proving things
-- by induction on finite sets
def swap_naturals (a b x: mynat): mynat
:= if x = a then b else if x = b then a else x

theorem swap_well_defined
(n a b: mynat) (ha: a < n) (hb: b < n):
well_defined (zero_to n) (zero_to n) (swap_naturals a b) :=
begin
  intro x,
  assume hx,
  unfold swap_naturals,
  by_cases hxa: x = a, {
    rw if_pos hxa,
    from hb,
  }, {
    rw if_neg hxa,
    by_cases hxb: x = b, {
      rw if_pos hxb,
      from ha,
    }, {
      rw if_neg hxb,
      from hx,
    },
  },
end

-- candidate for wlog_le? It's not clear because
-- we can have a = b
theorem swap_injective
(n a b: mynat) (ha: a < n) (hb: b < n):
injective (swap_well_defined n a b ha hb) :=
begin
  intros x y,
  assume hx hy,
  unfold swap_naturals,
  assume hswap_xy,
  by_cases hxy: x = y, {
    assumption,
  }, {
    exfalso,
    by_cases hxa: x = a, {
      rw if_pos hxa at hswap_xy,
      by_cases hya: y = a, {
        from hxy (eq.trans hxa hya.symm),
      }, {
        rw if_neg hya at hswap_xy,
        by_cases hyb: y = b, {
          rw if_pos hyb at hswap_xy,
          from hya (hswap_xy ▸ hyb),
        }, {
          rw if_neg hyb at hswap_xy,
          from hyb hswap_xy.symm,
        },
      },
    }, {
      rw if_neg hxa at hswap_xy,
      by_cases hxb: x = b, {
        rw if_pos hxb at hswap_xy,
        by_cases hya: y = a, {
          rw if_pos hya at hswap_xy,
          from (hswap_xy ▸ hxa) hxb,
        }, {
          rw if_neg hya at hswap_xy,
          by_cases hyb: y = b, {
            from (hyb ▸ hxy) hxb,
          }, {
            rw if_neg hyb at hswap_xy,
            from hya hswap_xy.symm,
          },
        },
      }, {
        rw if_neg hxb at hswap_xy,
        by_cases hya: y = a, {
          rw if_pos hya at hswap_xy,
          from hxb hswap_xy,
        }, {
          rw if_neg hya at hswap_xy,
          by_cases hyb: y = b, {
            rw if_pos hyb at hswap_xy,
            from hxa hswap_xy,
          }, {
            rw if_neg hyb at hswap_xy,
            from hxy hswap_xy,
          },
        },
      },
    },
  },
end

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
    sorry,
  },
end

theorem no_injection_if_gt
(m n: mynat) (f: mynat → mynat)
(hmn: n < m)
(hwf: well_defined (zero_to m) (zero_to n) f):
¬injective hwf :=
begin
  assume hif,
  cases m, {
    from lt_nzero hmn,
  }, {
    have hwf': well_defined (zero_to (succ m)) (zero_to m) f, {
      apply wf_by_inclusion (zero_to (succ m)) (zero_to n) (zero_to m) hwf,
      from zero_to_le_subset _ _ (le_iff_lt_succ.mpr hmn),
    },
    have hif': injective hwf' := hif,
    from no_injection_from_zero_to_succ _ _ _ hif',
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

end myset
end hidden
