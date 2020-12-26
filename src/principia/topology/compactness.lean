import .topological_space
import .continuity

namespace hidden

namespace topological_space

variables {α β γ: Type}

open classical

local attribute [instance] classical.prop_decidable

def is_open_cover (X: topological_space α) (𝒰: myset (myset α)): Prop :=
𝒰 ⊆ X.is_open ∧ ⋃₀ 𝒰 = myset.univ

def is_cover_l (X: topological_space α) (𝒰: mylist (myset α)): Prop :=
mylist.reduce_d myset.union ∅ 𝒰 = myset.univ

def is_compact (X: topological_space α): Prop :=
∀ 𝒰: myset (myset α), is_open_cover X 𝒰 →
∃ 𝒱: mylist (myset α), mylist.for_all 𝒰 𝒱 ∧ is_cover_l X 𝒱

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
          from rfl,
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

-- very suspicious
lemma list_intersection_iff_forall
(𝒱': mylist (myset α)) (y: α):
y ∈ mylist.reduce_d myset.intersection myset.univ 𝒱' ↔
mylist.for_all (λ V', y ∈ V') 𝒱' :=
begin
  split, {
    assume hyV',
    induction 𝒱' with V' V's ih_V's, {
      trivial,
    }, {
      split, {
        from hyV'.left,
      }, {
        apply ih_V's,
        from hyV'.right,
      },
    },
  }, {
    assume hyV',
    induction 𝒱' with V' V's ih_V's, {
      trivial,
    }, {
      split, {
        from hyV'.left,
      }, {
        apply ih_V's,
        from hyV'.right,
      },
    },
  },
end

lemma list_union_iff_exists
(𝒱': mylist (myset α)) (y: α):
y ∈ mylist.reduce_d myset.union ∅ 𝒱' ↔
mylist.for_some (λ V', y ∈ V') 𝒱' :=
begin
  split, {
    assume hyV',
    induction 𝒱' with V' V's ih_V's, {
      exfalso, from hyV',
    }, {
      cases hyV' with hyV' hyV', {
        left,
        from hyV',
      }, {
        right,
        apply ih_V's,
        from hyV',
      }
    },
  }, {
    assume hyV',
    induction 𝒱' with V' V's ih_V's, {
      exfalso, from hyV',
    }, {
      cases hyV' with hyV' hyV', {
        left,
        from hyV',
      }, {
        right,
        apply ih_V's,
        from hyV',
      }
    },
  },
end

-- not sure if this is optimal
-- but idk how else to construct things in the middle of a proof
private def is_raised_seq
(X: topological_space α) (Y: myset α)
(𝒰: myset (myset α)):
Π 𝒱: mylist (myset (subtype Y)),
Π (hWV: mylist.for_all ({W :
     myset (subtype Y) | (X.subspace_topology Y).is_open W ∧
     ∃ (U : myset α), Y.subtype_restriction U = W ∧ U ∈ 𝒰}) 𝒱),
mylist (myset α) → Prop
| mylist.empty _ mylist.empty := true
| mylist.empty _ (V' :: V's) := false
| (V :: Vs) _ mylist.empty := false
| (V :: Vs) h (V' :: V's) :=
  V' ∈ 𝒰 ∧
  (subspace_topology X Y).is_open V ∧
  myset.subtype_restriction Y V' = V ∧
  is_raised_seq Vs h.right V's

private lemma raised_seq_exists
(X: topological_space α) (Y: myset α) (𝒰: myset (myset α))
(𝒱: mylist (myset (subtype Y)))
(hWV: mylist.for_all ({W :
     myset (subtype Y) | (X.subspace_topology Y).is_open W ∧
     ∃ (U : myset α), Y.subtype_restriction U = W ∧ U ∈ 𝒰}) 𝒱)
(hVo: mylist.for_all (subspace_topology X Y).is_open 𝒱):
∃ 𝒱': mylist (myset α),
  is_raised_seq X Y 𝒰 𝒱 hWV 𝒱' :=
begin
  induction 𝒱 with V Vs ih_V, {
    existsi mylist.empty,
    trivial,
  }, {
    cases ih_V hWV.right hVo.right with V's hV's,
    cases hWV.left with V'' hV'',
    cases hV'' with V' hV',
    existsi V' :: V's,
    split, {
      from hV'.right,
    }, split, {
      assumption,
    }, split, {
      from hV'.left,
    }, {
      assumption,
    },
  },
end

private lemma raised_seq_U
(X: topological_space α) (Y: myset α) (𝒰: myset (myset α))
(𝒱: mylist (myset (subtype Y)))
(hWV: mylist.for_all ({W :
     myset (subtype Y) | (X.subspace_topology Y).is_open W ∧
     ∃ (U : myset α), Y.subtype_restriction U = W ∧ U ∈ 𝒰}) 𝒱)
(𝒱': mylist (myset α))
(hrV': is_raised_seq X Y 𝒰 𝒱 hWV 𝒱'):
mylist.for_all 𝒰 𝒱' :=
begin
  induction 𝒱' with V' V's ih_V' generalizing 𝒱, {
    trivial,
  }, {
    cases 𝒱 with V Vs, {
      exfalso, from hrV',
    }, {
      split, {
        from hrV'.left,
      }, {
        apply ih_V' _ hWV.right,
        from hrV'.right.right.right,
      },
    },
  },
end

private lemma raised_subset
(X: topological_space α) (Y: myset α) (𝒰: myset (myset α))
(𝒱: mylist (myset (subtype Y)))
(hWV: mylist.for_all ({W :
     myset (subtype Y) | (X.subspace_topology Y).is_open W ∧
     ∃ (U : myset α), Y.subtype_restriction U = W ∧ U ∈ 𝒰}) 𝒱)
(𝒱': mylist (myset α))
(hrV': is_raised_seq X Y 𝒰 𝒱 hWV 𝒱')
(x: α) (hYx: Y x)
(hxV: (⟨x, hYx⟩: subtype Y) ∈ mylist.reduce_d myset.union ∅ 𝒱):
x ∈ mylist.reduce_d myset.union ∅ 𝒱' :=
begin
  rw list_union,
  rw list_union at hxV,
  cases hxV with V hV,
  cases hV with hV hxV,
  have hWV' := hWV,
  rw mylist.for_all_iff_forall at hWV,
  cases (hWV V hV).right with V' hV',
  sorry,
end

theorem compact_subspace_cover
(X: topological_space α) (Y: myset α)
(hYcpct: is_compact (subspace_topology X Y)):
∀ 𝒰: myset (myset α),
  𝒰 ⊆ X.is_open →
  Y ⊆ ⋃₀ 𝒰 →
∃ 𝒱: mylist (myset α),
  mylist.for_all 𝒰 𝒱 ∧
  Y ⊆ mylist.reduce_d myset.union ∅ 𝒱 :=
begin
  intro 𝒰,
  assume hUo,
  assume hUYcov,
  let 𝒲 :=
      {W: myset (subtype Y) |
        (subspace_topology X Y).is_open W ∧
        ∃ U: myset α,
          Y.subtype_restriction U = W ∧
          U ∈ 𝒰},
  have step1 := hYcpct 𝒲,
  have hWYcov: (X.subspace_topology Y).is_open_cover 𝒲, {
    split, {
      intro W,
      assume hWW,
      from hWW.left,
    }, {
      apply funext,
      intro x,
      apply propext,
      split; assume hx, {
        trivial,
      }, {
        cases hUYcov x x.property with U hU,
        cases hU with hU hxU,
        existsi Y.subtype_restriction U,
        split, {
          split, {
            existsi U,
            split, {
              from hUo U hU,
            }, {
              refl,
            },
          }, {
            existsi U,
            split, {
              refl,
            }, {
              assumption,
            },
          },
        }, {
          from hxU,
        },
      },
    },
  },
  have step2 := step1 hWYcov,
  cases step2 with 𝒱 hV,
  have step4: mylist.for_all (X.subspace_topology Y).is_open 𝒱, {
    cases hV with hV garbage,
    clear garbage,
    induction 𝒱 with V Vs ih_V, {
      trivial,
    }, {
      split, {
        from hV.left.left,
      }, {
        apply ih_V, {
          from hV.right,
        },
      },
    },
  },
  have step3 := raised_seq_exists X Y 𝒰 𝒱 hV.left,
  have step5 := step3 step4,
  cases step5 with 𝒱' hV',
  existsi 𝒱',
  split, {
    apply raised_seq_U X Y 𝒰 𝒱 hV.left,
    from hV',
  }, {
    intro x,
    assume hYx,
    have hxV: (⟨x, hYx⟩: subtype Y) ∈ (mylist.reduce_d myset.union ∅ 𝒱), {
      have := hV.right,
      unfold is_cover_l at this,
      rw this,
      trivial,
    },
    from raised_subset X Y 𝒰 𝒱 hV.left 𝒱' hV' x hYx hxV,
  },
end

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

private def is_corresponding_subcov
(X: topological_space α) (x: α)
(U: myset α):
Π (𝒱: mylist (myset α)),
mylist (myset α) → Prop
| mylist.empty mylist.empty := true
| (V :: Vs) mylist.empty := false
| mylist.empty (V' :: V's) := false
| (V :: Vs) (V' :: V's) :=
  is_corresponding_subcov Vs V's ∧
  ∃ (y : α),
    y ∈ U ∧ X.is_open V ∧ X.is_open V' ∧ y ∈ V ∧ x ∈ V' ∧ V ∩ V' = ∅

private lemma corresponding_subcov_forall
(X: topological_space α) (x: α)
(U: myset α)
(𝒱: mylist (myset α))
(𝒱': mylist (myset α))
(hcor: is_corresponding_subcov X x U 𝒱 𝒱'):
mylist.for_all
  (λ V', ∃ (y : α),
    y ∈ U ∧ X.is_open V' ∧ x ∈ V')
  𝒱' :=
begin
  revert 𝒱,
  induction 𝒱' with V' V's ih_V's, {
    intros,
    trivial,
  }, {
    intros,
    cases 𝒱 with V Vs, {
      exfalso,
      from hcor,
    }, {
      split, {
        cases hcor.right with y hy,
        existsi y,
        repeat {split, cc},
        cc,
      }, {
        apply ih_V's Vs hcor.left,
      },
    },
  },
end

private lemma corresponding_subcov_forall2
(X: topological_space α) (x: α)
(U: myset α)
(𝒱: mylist (myset α))
(𝒱': mylist (myset α))
(hcor: is_corresponding_subcov X x U 𝒱 𝒱'):
mylist.for_all
  (λ V', ∃ (y : α) (V: myset α), mylist.contains V 𝒱 ∧
    y ∈ U ∧ X.is_open V ∧ X.is_open V' ∧ y ∈ V ∧ x ∈ V' ∧ V ∩ V' = ∅)
  𝒱' :=
begin
  revert 𝒱,
  induction 𝒱' with V' V's ih_V's, {
    intros,
    trivial,
  }, {
    intros,
    cases 𝒱 with V Vs, {
      exfalso,
      from hcor,
    }, {
      split, {
        cases hcor.right with y hy,
        existsi y,
        existsi V,
        repeat {split, cc},
        split, left,
        from rfl,
        from hy,
      }, {
        have := ih_V's Vs hcor.left,
        apply (mylist.for_all_iff_forall _ _).mpr,
        rw mylist.for_all_iff_forall at this,
        intro V'',
        assume hV''Vs,
        cases this V'' hV''Vs with y hy,
        cases hy with W hW,
        existsi y,
        existsi W,
        split, right,
        from hW.left,
        from hW.right,
        -- apply ih_V's Vs hcor.left,
      },
    },
  },
end

private lemma corresponding_subcov_forall2_symm
(X: topological_space α) (x: α)
(U: myset α)
(𝒱: mylist (myset α))
(𝒱': mylist (myset α))
(hcor: is_corresponding_subcov X x U 𝒱 𝒱'):
mylist.for_all
  (λ V, ∃ (y : α) (V': myset α), mylist.contains V' 𝒱' ∧
    y ∈ U ∧ X.is_open V ∧ X.is_open V' ∧ y ∈ V ∧ x ∈ V' ∧ V ∩ V' = ∅)
  𝒱 :=
begin
  revert 𝒱',
  induction 𝒱 with V Vs ih_Vs, {
    intros,
    trivial,
  }, {
    intros,
    cases 𝒱' with V' V's, {
      exfalso,
      from hcor,
    }, {
      split, {
        cases hcor.right with y hy,
        existsi y,
        existsi V',
        repeat {split, cc},
        split, left,
        from rfl,
        from hy,
      }, {
        have := ih_Vs V's hcor.left,
        apply (mylist.for_all_iff_forall _ _).mpr,
        rw mylist.for_all_iff_forall at this,
        intro V'',
        assume hV''Vs,
        cases this V'' hV''Vs with y hy,
        cases hy with W hW,
        existsi y,
        existsi W,
        split, right,
        from hW.left,
        from hW.right,
        -- apply ih_V's Vs hcor.left,
      },
    },
  },
end

private lemma exists_corresponding_subcov
(X: topological_space α) (x: α)
(U: myset α)
(𝒱: mylist (myset α))
(hVU: mylist.for_all
  ({V :
     myset α | ∃ (y : α) (W : myset α),
     y ∈ U ∧ X.is_open V ∧ X.is_open W ∧ y ∈ V ∧ x ∈ W ∧ V ∩ W = ∅}) 𝒱):
∃ 𝒱': mylist (myset α),
  is_corresponding_subcov X x U 𝒱 𝒱' :=
begin
  induction 𝒱 with V Vs ih_Vs, {
    existsi mylist.empty,
    trivial,
  }, {
    cases ih_Vs hVU.right with V's hV's,
    cases hVU.left with y hV',
    cases hV' with V' hV',
    existsi V' :: V's,
    split, {
      from hV's,
    }, {
      existsi y,
      from hV',
    },
  },
end

theorem compact_in_hausdorff
(X: topological_space α) (U: myset α)
(hUcpct: is_compact (subspace_topology X U))
(h_ausdorff: is_hausdorff X):
X.is_closed U :=
begin
  unfold is_closed,
  rw open_iff_neighbourhood_forall,
  intro x,
  assume hxUc,
  let 𝒰 :=
      {V: myset α | ∃ (y: α) (W: myset α),
        y ∈ U ∧
        X.is_open V ∧ X.is_open W ∧ y ∈ V ∧ x ∈ W ∧ V ∩ W = ∅},
  have step1 := compact_subspace_cover X U hUcpct 𝒰,
  have step2: 𝒰 ⊆ X.is_open, {
    intro V,
    assume hVU,
    cases hVU with y hVU,
    cases hVU with W hVU,
    from hVU.right.left,
  },
  have step3: U ⊆ ⋃₀ 𝒰, {
    intro y,
    assume hUy,
    cases h_ausdorff x y
      begin
        assume hxy,
        rw hxy at hxUc,
        contradiction,
      end with V1 hVy,
    cases hVy with V2 hVy,
    existsi V2,
    split, {
      existsi y,
      existsi V1,
      split, assumption,
      repeat {split, cc},
      rw ←hVy.right.right.right.right,
      apply myset.setext,
      intro x,
      from ⟨and.symm, and.symm⟩,
    }, {
      cc,
    },
  },
  cases step1 step2 step3 with 𝒱 hV,
  cases exists_corresponding_subcov X x U 𝒱 hV.left with 𝒱' hV',
  have hV'fa := corresponding_subcov_forall X x U 𝒱 𝒱' hV',
  existsi mylist.reduce_d myset.intersection myset.univ 𝒱',
  split, {
    apply finite_open_intersection_open,
    rw mylist.for_all_iff_forall,
    intro V',
    assume hV'inV,
    rw mylist.for_all_iff_forall at hV,
    rw mylist.for_all_iff_forall at hV'fa,
    cases hV'fa V' hV'inV with _ h,
    from h.right.left,
  }, split, {
    cases hV with hV garbage,
    clear garbage,
    revert 𝒱,
    induction 𝒱' with V' V's ih_V's, {
      intros,
      trivial,
    }, {
      intros,
      split, {
        cases hV'fa.left with _ h,
        from h.right.right,
      }, {
        cases 𝒱 with V Vs, {
          exfalso,
          from hV',
        }, {
          apply ih_V's _ Vs, {
            from hV'.left,
          }, {
            from hV.right,
          }, {
            from hV'fa.right,
          },
        },
      },
    },
  }, {
    intro y,
    assume hV'y,
    assume hUy,
    have hV'fa2 := corresponding_subcov_forall2 X x U 𝒱 𝒱' hV',
    have := (list_union_iff_exists 𝒱 y).mp (hV.right y hUy),
    rw mylist.for_some_iff_exists at this,
    cases this with Z hZ,
    cases hZ with hZ hyZ,
    unfold mylist.contains at hZ,
    rw mylist.for_some_iff_exists at hZ,
    cases hZ with Z' hZ,
    cases hV with hVsubcovU hUsubV,
    rw mylist.for_all_iff_forall at hVsubcovU,
    have := hVsubcovU Z' hZ.left,
    cases this with z hz,
    cases hz with W hW,
    have hV'fa2s := corresponding_subcov_forall2_symm X x U 𝒱 𝒱' hV',
    rw mylist.for_all_iff_forall at hV'fa2s,
    cases hV'fa2s Z' hZ.left with z' hz',
    cases hz' with V' hzV',
    have := (list_intersection_iff_forall _ _).mp hV'y,
    rw mylist.for_all_iff_forall at this,
    have hyV' := this V' hzV'.left,
    suffices hhhhh: y ∈ Z' ∩ V', {
      rw hzV'.right.right.right.right.right.right at hhhhh,
      from hhhhh,
    }, {
      split, {
        rw ←hZ.right,
        assumption,
      }, {
        assumption,
      },
    },
  },
end

theorem surjective_image_compact
(X: topological_space α) (Y: topological_space β)
(hXcpct: is_compact X)
(f: α → β) (hcf: is_continuous X Y f) (hsurj: function.surjective f):
is_compact Y :=
begin
  intro 𝒰,
  assume hUcov,
  have step1 := hXcpct (myset.image (myset.inverse_image f) 𝒰),
  have step2: X.is_open_cover (myset.image (myset.inverse_image f) 𝒰), {
    split, {
      intro V,
      assume hV,
      cases hV with V' hV',
      rw ←hV'.right,
      apply hcf,
      apply hUcov.left,
      from hV'.left,
    }, {
      apply funext,
      intro x,
      apply propext,
      split; assume hx, {
        trivial,
      }, {
        have: f x ∈ ⋃₀ 𝒰, {
          rw hUcov.right,
          trivial,
        },
        cases this with U hU,
        cases hU with hU hfxU,
        existsi myset.inverse_image f U,
        split, {
          existsi U,
          split, {
            from hU,
          }, {
            refl,
          },
        }, {
          from hfxU,
        },
      },
    },
  },
  have step3 := step1 step2,
  cases step3 with 𝒱' hV',
  sorry,
end

theorem image_compact
(X: topological_space α) (Y: topological_space β)
(hXcpct: is_compact X)
(f: α → β) (hcf: is_continuous X Y f):
is_compact (Y.subspace_topology (myset.imageu f)) :=
begin
  apply surjective_image_compact X _ hXcpct (myset.function_restrict_to_image f), {
    apply continuous_to_image,
    from hcf,
  }, {
    intro y,
    cases y.property with x hx,
    existsi x,
    apply subtype.eq,
    from hx,
  },
end

-- could do with some theorems about preimages and images
-- of inverses
theorem topological_inverse_function_theorem
(X: topological_space α) (Y: topological_space β)
(hXcpct: is_compact X) (h_ausdorff: is_hausdorff Y)
(f: α → β) (g: β → α) (hcf: is_continuous X Y f)
(right_inv: f ∘ g = id)
(left_inv: g ∘ f = id):
is_continuous Y X g :=
begin
  rw continuous_iff_closed_preimage,
  intro U,
  assume hUo,
  have: myset.inverse_image g U = myset.image f U, {
    apply funext,
    intro x,
    apply propext,
    split; assume hx, {
      existsi g x,
      split, {
        from hx,
      }, {
        change (f ∘ g) x = x,
        rw right_inv,
        refl,
      },
    }, {
      cases hx with y hy,
      have: g x = y, {
        rw ←hy.right,
        change (g ∘ f) y = y,
        rw left_inv,
        refl,
      },
      rw ←this at hy,
      from hy.left,
    },
  },
  rw this, clear this,
  apply compact_in_hausdorff, {
    apply surjective_image_compact
        (X.subspace_topology U)
        (Y.subspace_topology (myset.image f U)) _
        (myset.function_restrict_to_set_image f U), {
      rw myset.restrict_to_set_image_composition,
      apply composition_continuous
          (X.subspace_topology U)
          (Y.subspace_topology (myset.imageu (λ x: subtype U, f x.val)))
          (Y.subspace_topology (myset.image f U)), {
        apply continuous_to_image,
        apply composition_continuous
            _ _ _ _ _ (inclusion_continuous _ _),
        from hcf,
      }, {
        intro U,
        assume hUo,
        cases hUo with V' hV',
        existsi V',
        split, {
          from hV'.left,
        }, {
          rw hV'.right,
          refl, -- thank the lord
        },
      },
    }, {
      intro y,
      cases y.property with y' hy',
      existsi (⟨y', hy'.left⟩: subtype U),
      apply subtype.eq,
      -- rw won't play ball >:(
      transitivity (f y'), {
        refl,
      }, {
        from hy'.right,
      },
    }, {
      apply closed_in_compact, {
        from hXcpct,
      }, {
        from hUo,
      },
    },
  }, {
    from h_ausdorff,
  },
end

end topological_space

end hidden
