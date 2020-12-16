-- vim: ts=2 sw=0 sts=-1 et ai tw=70

import ..logic

namespace hidden

universes u v w

-- A set of elements of type α is a function from elements of type α
-- to propositions
def myset (α : Type u) := α → Prop

 -- Not sure if we want this, but I don't think it hurts
namespace myset

-- Need u and v to be most general
variables {α : Type u} {β : Type v}

def mem (a : α) (s : myset α) : Prop := s a
instance: has_mem α (myset α) := ⟨myset.mem⟩

theorem mem_def {a : α} {s : myset α} : a ∈ s = s a := rfl

theorem setext (A B : myset α) : (∀ x : α, x ∈ A ↔ x ∈ B) → A = B :=
begin
  assume h,
  apply funext,
  intro x,
  apply propext,
  from h x,
end

def subset (s : myset α) (t : myset α) : Prop :=
∀ a : α, s a → t a
-- Use \subseteq
instance: has_subset (myset α) := ⟨myset.subset⟩

@[refl]
theorem subset_refl (s: myset α):
s ⊆ s :=
begin
  intro x,
  assume h,
  assumption,
end

def power_set (s : myset α) : myset (myset α) :=
λ t, t ⊆ s

def intersection (s : myset α) (t : myset α) : myset α :=
λ a, s a ∧ t a
instance: has_inter (myset α) := ⟨intersection⟩
def union (s : myset α) (t : myset α) : myset α :=
λ a, s a ∨ t a
instance: has_union (myset α) := ⟨union⟩

-- Construct an empty set with type α
def empty_of (α : Type u) : myset α := λ a, false
def empty {α : Type u} (s : myset α) : Prop := ∀ a : α, ¬(a ∈ s)
def all_of (α : Type u) : myset α := λ a, true

theorem exists_iff_nempty {s : myset α} :
(∃ x, x ∈ s) ↔ ¬empty s :=
begin
  split; assume h, {
    assume hemp,
    cases h with x hx,
    have := hemp x,
    contradiction,
  }, {
    unfold myset.empty at h,
    rw not_forall at h,
    cases h with k hk,
    existsi k,
    rw not_not at hk,
    assumption,
  },
end

-- Set product, gives myset (α × β)
def set_prod (U : myset α) (V : myset β) : myset (α × β) :=
{t | t.1 ∈ U ∧ t.2 ∈ V}

notation U × V := set_prod U V

instance : has_emptyc (myset α) :=
⟨λ a, false⟩

theorem in_empty_false (x : α) : x ∈ (∅ : myset α) → false :=
begin
  assume hx,
  assumption,
end

theorem empty_iff_eq_empty {s: myset α}: empty s ↔ s = ∅ :=
begin
  split; assume h, {
    apply funext,
    intro a,
    have := h a,
    apply propext,
    split, {
      assume hs, contradiction,
    }, {
      assume he,
      exfalso,
      from he,
    },
  }, {
    intro a,
    assume hs,
    rw h at hs,
    from hs,
  },
end

theorem exists_iff_neq_empty {S: myset α}:
(∃ x, x ∈ S) ↔ S ≠ ∅ :=
begin
  have: S ≠ ∅ ↔ ¬S = ∅ := iff.rfl,
  rw this,
  rw ←empty_iff_eq_empty,
  rw ←exists_iff_nempty,
end

@[reducible]
def sUnion (s : myset (myset α)) : myset α := {t | ∃ a ∈ s, t ∈ a}
prefix `⋃₀`:120 := sUnion

@[reducible]
def sIntersection (s : myset (myset α)) : myset α :=
{t | ∀ a ∈ s, t ∈ a}
prefix `⋂₀`:120 := sIntersection

def univ : myset α :=
λ a, true

def singleton (x: α): myset α :=
{y | y = x}

theorem singleton_eq (x y: α): y ∈ singleton x → y = x :=
begin
  assume hyx,
  from hyx,
end

def image {α β : Type} (f : α → β) (U : myset α) := {b | ∃ a, a ∈ U ∧ f a = b}

def inverse_image {α β : Type} (f : α → β) (V : myset β) := {a | f a ∈ V}

theorem inverse_image_of_image
{α β : Type} (f: α → β) (U : myset α):
U ⊆ inverse_image f (image f U) :=
begin
  intro x,
  assume hx,
  existsi x,
  split, assumption, trivial,
end

theorem image_of_inverse_image
{α β : Type} (f: α → β) (U : myset β):
image f (inverse_image f U) ⊆ U :=
begin
  intro x,
  assume hx,
  cases hx with y hy,
  rw ←hy.right,
  from hy.left,
end

theorem subset_empty_impl_empty
{α: Type} (U: myset α):
U ⊆ ∅ → U = ∅ :=
begin
  assume hUe,
  apply funext,
  intro x,
  apply propext,
  split; assume h, {
    from hUe _ h,
  }, {
    exfalso, from h,
  },
end

theorem univ_subset_impl_univ
{α: Type} (U: myset α):
myset.univ ⊆ U → U = myset.univ :=
begin
  assume h,
  apply funext,
  intro x,
  apply propext,
  split; assume hux, {
    trivial,
  }, {
    from h x trivial,
  },
end

theorem image_nonempty
{α β : Type} (f: α → β) (U: myset α):
U ≠ ∅ → image f U ≠ ∅ :=
begin
  assume hUne,
  assume hpreUe,
  rw ←empty_iff_eq_empty at hpreUe,
  change ¬(U = ∅) at hUne,
  rw ←empty_iff_eq_empty at hUne,
  rw ←exists_iff_nempty at hUne,
  cases hUne with x hx,
  apply hpreUe (f x),
  existsi x,
  split, assumption, refl,
end

theorem image_empty
{α β : Type} (f: α → β) (U: myset α):
U = ∅ → image f U = ∅ :=
begin
  assume hUe,
  apply funext,
  intro x,
  apply propext,
  split; assume h, {
    cases h with y hy,
    rw hUe at hy,
    from hy.left,
  }, {
    exfalso, from h,
  },
end

theorem inverse_image_empty
{α β : Type} (f: α → β) (U: myset β):
U = ∅ → inverse_image f U = ∅ :=
begin
  assume hUe,
  apply setext,
  intro x,
  split; assume h, {
    rw hUe at h,
    from h,
  }, {
    exfalso, from h,
  },
end

theorem inverse_image_intersection
{α β : Type} (f: α → β) (U V: myset β):
inverse_image f (U ∩ V) = inverse_image f U ∩ inverse_image f V :=
begin
  refl,
end

theorem inverse_image_union
{α β : Type} (f: α → β) (U V: myset β):
inverse_image f (U ∪ V) = inverse_image f U ∪ inverse_image f V :=
begin
  refl,
end

theorem inverse_image_sUnion
{α β : Type} (f: α → β) (S: myset (myset β)):
inverse_image f ⋃₀ S = ⋃₀ image (inverse_image f) S :=
begin
  apply setext,
  intro x,
  split; assume hx, {
    cases hx with U hU,
    cases hU with hU hxU,
    existsi (inverse_image f U),
    split, {
      existsi U,
      split, {
        assumption,
      }, {
        refl,
      },
    }, {
      assumption,
    },
  }, {
    cases hx with U hU,
    cases hU with hU hxU,
    cases hU with V hV,
    existsi V,
    split, {
      from hV.left,
    }, {
      rw ←hV.right at hxU,
      from hxU,
    },
  },
end

theorem inverse_image_sIntersection
{α β : Type} (f: α → β) (S: myset (myset β)):
inverse_image f ⋂₀ S = ⋂₀ image (inverse_image f) S :=
begin
  apply setext,
  intro x,
  split; assume hx, {
    intro U,
    assume hUS,
    cases hUS with V hV,
    rw ←hV.right,
    from hx V hV.left,
  }, {
    intro U,
    assume hUs,
    apply hx,
    existsi U,
    split, {
      assumption,
    }, {
      refl,
    },
  },
end

theorem image_intersection
{α β : Type} (f: α → β) (U V: myset α):
image f (U ∩ V) ⊆ image f U ∩ image f V :=
begin
  intro x,
  assume hx,
  cases hx with y hy,
  split, {
    existsi y,
    split, {
      from hy.left.left,
    }, {
      from hy.right,
    },
  }, {
    existsi y,
    split, {
      from hy.left.right,
    }, {
      from hy.right,
    },
  },
end

theorem image_union
{α β : Type} (f: α → β) (U V: myset α):
image f (U ∪ V) = image f U ∪ image f V :=
begin
  apply setext,
  intro x,
  split; assume hx, {
    cases hx with y hy,
    cases hy with hyUV hfyx,
    rw ←hfyx,
    cases hyUV with hyU hyV, {
      left,
      existsi y,
      split, {
        assumption,
      }, {
        refl,
      },
    }, {
      right,
      existsi y,
      split, {
        assumption,
      }, {
        refl,
      },
    },
  }, {
    cases hx with hxfU hxfV, {
      cases hxfU with y hy,
      existsi y,
      split, {
        left,
        from hy.left,
      }, {
        from hy.right,
      },
    }, {
      cases hxfV with y hy,
      existsi y,
      split, {
        right,
        from hy.left,
      }, {
        from hy.right,
      },
    },
  },
end

theorem image_sUnion
{α β : Type} (f: α → β) (S: myset (myset α)):
image f ⋃₀ S = ⋃₀ image (image f) S :=
begin
  apply setext,
  intro x,
  split; assume hx, {
    cases hx with y hy,
    cases hy with hy hfyx,
    cases hy with U hU,
    cases hU with hU hyU,
    existsi image f U,
    split, {
      existsi U,
      split, {
        assumption,
      }, {
        refl,
      },
    }, {
      existsi y,
      split; assumption,
    },
  }, {
    cases hx with U hU,
    cases hU with hU hxU,
    cases hU with V hV,
    rw ←hV.right at hxU,
    cases hxU with y hy,
    existsi y,
    split, {
      existsi V,
      split, {
        from hV.left,
      }, {
        from hy.left,
      },
    }, {
      from hy.right,
    },
  },
end

theorem image_sIntersection
{α β : Type} (f: α → β) (S: myset (myset α)):
image f ⋂₀ S ⊆ ⋂₀ image (image f) S :=
begin
  intro x,
  assume hx,
  intro U,
  assume hU,
  cases hU with V hV,
  cases hx with y hy,
  rw ←hy.right,
  rw ←hV.right,
  existsi y,
  split, {
    apply hy.left,
    from hV.left,
  }, {
    refl,
  },
end

theorem inverse_image_composition
{α β γ: Type} (f: α → β) (g: β → γ) (U: myset γ):
inverse_image (g ∘ f) U =
inverse_image f (inverse_image g U) :=
begin
  apply setext,
  intro x,
  refl,
end

theorem image_composition
{α β γ: Type} (f: α → β) (g: β → γ) (U: myset α):
image (g ∘ f) U =
image g (image f U) :=
begin
  apply setext,
  intro x,
  split; assume h, {
    cases h with y hy,
    existsi f y,
    split, {
      existsi y, {
        split, {
          from hy.left,
        }, {
          refl,
        },
      },
    }, {
      from hy.right,
    },
  }, {
    cases h with y hy,
    cases hy with hy hgyx,
    cases hy with z hz,
    existsi z,
    split, {
      from hz.left,
    }, {
      change g (f z) = x,
      rw hz.right,
      assumption,
    },
  },
end

theorem image_subset
{α β: Type} (f: α → β) (U V: myset α):
U ⊆ V → image f U ⊆ image f V :=
begin
  assume hUV,
  intro x,
  assume hximf,
  cases hximf with y hy,
  existsi y,
  split, {
    apply hUV,
    from hy.left,
  }, {
    from hy.right,
  },
end

theorem inverse_image_subset
{α β: Type} (f: α → β) (U V: myset β):
U ⊆ V → inverse_image f U ⊆ inverse_image f V :=
begin
  assume hUV,
  intro x,
  assume hximf,
  apply hUV,
  from hximf,
end

theorem inverse_image_of_image_of_univ
{α β : Type} (f: α → β):
myset.univ = inverse_image f (image f myset.univ) :=
begin
  symmetry,
  apply univ_subset_impl_univ,
  apply inverse_image_of_image,
end

def compl (s : myset α) : myset α :=
{a | a ∉ s}

theorem inverse_image_compl
{α β: Type} (S: myset β) (f: α → β):
inverse_image f S.compl = (inverse_image f S).compl :=
begin
  refl,
end

theorem compl_compl
{α: Type} (S: myset α) [∀ x: α, decidable (x ∈ S)]:
S.compl.compl = S :=
begin
  apply setext,
  intro x,
  from decidable.not_not_iff _,
end

theorem compl_cancel {α: Type} (S: myset α) (T: myset α) [∀ x: α, decidable (x ∈ S)]
[∀ x: α, decidable (x ∈ T)]:
S.compl = T.compl → S = T :=
begin
  assume h,
  rw [←compl_compl S, ←compl_compl T, h],
end

theorem compl_intersection {α : Type} (S T : myset α) :
(S ∩ T).compl = S.compl ∪ T.compl :=
begin
  apply setext,
  intro x,
  from not_and_distrib,
end

-- Stronk decidability
theorem compl_sIntersection {α : Type} (σ : myset (myset α)) [∀ (x : α) (S: myset α), decidable (x ∈ S)] :
(⋂₀ σ).compl = ⋃₀ (image compl σ) :=
begin
  apply setext,
  intro x,
  split; assume h, {
    change ¬(∀ S ∈ σ, x ∈ S) at h,
    rw not_forall at h,
    cases h with S hS,
    rw not_imp at hS,
    existsi S.compl,
    suffices : S.compl ∈ image compl σ,
      existsi this,
      from hS.right,
    existsi S,
    split,
      from hS.left,
    refl,
  }, {
    change ¬(∀ S ∈ σ, x ∈ S),
    rw not_forall,
    change ∃ S ∈ (image compl σ), x ∈ S at h,
    cases h with S hS,
    cases hS with hS hxS,
    existsi S.compl,
    assume h,
    apply h,
      cases hS with T hT,
      rw [hT.right.symm, compl_compl],
      from hT.left,
    from hxS,
  },
end

section

open classical

local attribute [instance] classical.prop_decidable

theorem compl_sUnion {α : Type} (σ : myset (myset α)) :
(⋃₀ σ).compl = ⋂₀ (image compl σ) :=
begin
  apply compl_cancel,
  rw [compl_compl, compl_sIntersection],
  congr,
  apply setext,
  intro S,
  split; assume hS,
    existsi S.compl,
    split,
      existsi S,
      split,
        assumption,
      refl,
    rw compl_compl,
  cases hS with T hT,
  rw hT.right.symm,
  cases hT.left with U hU,
  rw [hU.right.symm, compl_compl],
  from hU.left,
end

theorem compl_subset_compl {α : Type}  (S T : myset α) :
S.compl ⊆ T.compl ↔ T ⊆ S :=
begin
  split; assume h,
    intros x hx,
    by_contradiction,
    from h _ a hx,
  intros x hx,
  assume hxT,
  from hx (h _ hxT),
end

end

theorem disjoint_iff_subset_compl {α : Type}  (S T : myset α) :
S ∩ T = ∅ ↔ S ⊆ T.compl :=
begin
  split; assume h,
    intros x hxS,
    assume hx,
    apply in_empty_false x, --??
    rw ←h,
    change x ∈ S ∧ x ∈ T,
    split,
      from hxS,
    from hx,
  apply setext,
  intro x,
  split; assume hx,
    exfalso,
    apply h _ hx.left,
    from hx.right,
  exfalso,
  assumption,
end

theorem intersection_comm {α : Type}  (S T : myset α) :
S ∩ T = T ∩ S :=
begin
  apply setext,
  intro x,
  split; from λ h, ⟨h.right, h.left⟩,
end

theorem subset_compl_symm {α : Type}  (S T : myset α) :
S ⊆ T.compl → T ⊆ S.compl :=
begin
  assume h,
  rwa [←disjoint_iff_subset_compl, intersection_comm, disjoint_iff_subset_compl],
end

-- Used to restrict some set to a subtype ("intersect" a set with a subtype)
def subtype_restriction (Y : myset α) (U : myset α) : myset (subtype Y) :=
{ w | ↑w ∈ U }

-- pffffff
def subtype_unrestriction (Y: myset α) (U: myset (subtype Y)): myset α :=
{x | ∃ hxS: x ∈ Y, (⟨x, hxS⟩: subtype Y) ∈ U}

def function_restrict_to_image
{α β: Type} (f: α → β): α → subtype (myset.image f myset.univ)
:= λ x, ⟨f x, ⟨x, ⟨true.intro, rfl⟩⟩⟩

theorem to_image_surjective
{α β: Type} (f: α → β):
(image (function_restrict_to_image f) univ) = univ :=
begin
  apply funext,
  intro x,
  apply propext,
  split; assume h, {
    trivial,
  }, {
    cases x.property with y hy,
    unfold image,
    existsi y,
    split, {
      trivial,
    }, {
      apply subtype.eq,
      rw ←hy.right,
      refl,
    },
  },
end

theorem nonempty_inverse_image_surjective
{α β: Type} (f: α → β) (U: myset (subtype (image f univ))):
U ≠ ∅ →
inverse_image (function_restrict_to_image f) U ≠ ∅ :=
begin
  assume hUne,
  assume hpreUe,
  rw ←empty_iff_eq_empty at hpreUe,
  change ¬(U = ∅) at hUne,
  rw ←empty_iff_eq_empty at hUne,
  rw ←exists_iff_nempty at hUne,
  cases hUne with x hx,
  cases x.property with y hy,
  apply hpreUe y,
  unfold inverse_image,
  have: x = ⟨f y, begin rw hy.right, from x.property end⟩, {
    apply subtype.eq,
    from hy.right.symm,
  },
  rw this at hx, clear this,
  from hx,
end

end myset

end hidden
