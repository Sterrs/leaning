import .topological_space

namespace hidden

namespace topological_space

variables {α β γ: Type}

open classical

local attribute [instance] classical.prop_decidable

def is_open_cover (X: topological_space α) (𝒰: myset (myset α)): Prop :=
𝒰 ⊆ X.is_open ∧ ⋃₀ 𝒰 = myset.univ

def is_cover_l (X: topological_space α) (𝒰: mylist (myset α)): Prop :=
mylist.reduce_d myset.union ∅ 𝒰 = myset.univ

theorem list_union (𝒰: mylist (myset α)):
mylist.reduce_d myset.union ∅ 𝒰 =
⋃₀ (λ x, 𝒰.contains x) :=
begin
  apply funext,
  intro x,
  apply propext,
  split; assume hx, {
    induction 𝒰 with U Us ih_U, {
      exfalso, from hx,
    }, {
      cases hx with hx hx, {
        existsi U,
        split, {
          left,
          refl,
        }, {
          assumption,
        },
      }, {
        cases ih_U hx with V hV,
        cases hV with hV hxV,
        existsi V,
        split, {
          right,
          from hV,
        }, {
          assumption,
        },
      },
    },
  }, {
    induction 𝒰 with U Us ih_U, {
      cases hx with V hV,
      cases hV with hV hxV,
      exfalso, from hV,
    }, {
      cases hx with V hV,
      cases hV with hV hxV,
      cases hV with hV hV, {
        left,
        rw ←hV,
        assumption,
      }, {
        right,
        apply ih_U,
        existsi V,
        split, {
          from hV,
        }, {
          assumption,
        },
      },
    },
  },
end

def is_compact (X: topological_space α): Prop :=
∀ 𝒰: myset (myset α), is_open_cover X 𝒰 →
∃ 𝒱: mylist (myset α), mylist.for_all 𝒰 𝒱 ∧ is_cover_l X 𝒱

-- could do with a bit of splitting up imho
theorem closed_in_compact
(X: topological_space α) (U: myset α)
(hXcpct: is_compact X) (hUcl: X.is_closed U):
is_compact (subspace_topology X U) :=
begin
  intro 𝒰,
  assume hUcov,
  have step1 :=
      hXcpct
        ((myset.singleton U.compl) ∪
         {V | X.is_open V ∧
              𝒰 (U.subtype_restriction V)}),
  have hcovX:
      X.is_open_cover
        ((myset.singleton U.compl) ∪
         {V | X.is_open V ∧
              𝒰 (U.subtype_restriction V)}), {
    split, {
      intro S,
      assume hS,
      cases hS with hS hS, {
        rw myset.singleton_eq _ _ hS,
        from hUcl,
      }, {
        from hS.left,
      },
    }, {
      apply funext,
      intro x,
      apply propext,
      split; assume hx, {
        trivial,
      }, {
        by_cases hxU: x ∈ U, {
          have: (⟨x, hxU⟩: subtype U) ∈ ⋃₀ 𝒰, {
            rw hUcov.right,
            trivial,
          },
          cases this with V hV,
          cases hV with hV hxV,
          cases hUcov.left V hV with V' hV',
          existsi V',
          split, {
            right,
            split, {
              from hV'.left,
            }, {
              rw hV'.right at hV,
              from hV,
            },
          }, {
            rw hV'.right at hxV,
            from hxV,
          },
        }, {
          existsi U.compl,
          split, {
            left,
            from rfl,
          }, {
            from hxU,
          },
        },
      },
    },
  },
  have step2 := step1 hcovX,
  cases step2 with 𝒱 hV,
  existsi mylist.map
      (myset.subtype_restriction U) 
      (mylist.filter (≠ U.compl) 𝒱),
  split, {
    cases hV with hV disaster,
    clear disaster,
    induction 𝒱 with V Vs ih_V, {
      trivial,
    }, {
      by_cases hVU: V = U.compl, {
        unfold mylist.filter,
        have: ¬(V ≠ U.compl), {
          assume h,
          contradiction,
        },
        rw if_neg this,
        apply ih_V,
        from hV.right,
      }, {
        unfold mylist.filter,
        rw if_pos hVU,
        split, {
          cases hV.left with hVl hVl, {
            contradiction,
          }, {
            from hVl.right,
          },
        }, {
          apply ih_V,
          from hV.right,
        },
      },
    },
  }, {
    cases hV with disaster hV,
    clear disaster,
    unfold is_cover_l,
    rw list_union,
    unfold is_cover_l at hV,
    rw list_union at hV,
    apply funext,
    intro x,
    apply propext,
    split; assume hx, {
      trivial,
    }, {
      have: x.val ∈ (myset.univ: myset α), {
        trivial,
      },
      rw ←hV at this,
      cases this with V hxV,
      cases hxV with hVV hxvV,
      existsi (myset.subtype_restriction U V),
      split, {
        apply mylist.contains_map,
        rw mylist.contains_filter,
        split, {
          from hVV,
        }, {
          assume hVUc,
          rw hVUc at hxvV,
          apply hxvV,
          from x.property,
        },
      }, {
        from hxvV,
      },
    },
  },
end

theorem compact_in_hausdorff
(X: topological_space α) (U: myset α)
(hUcpct: is_compact (subspace_topology X U))
(h_ausdorff: is_hausdorff X):
X.is_closed U :=
begin
  sorry
end

end topological_space

end hidden