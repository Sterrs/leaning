import .basic
import ..myset.basic

namespace hidden

def is_upper_bound (S : myset real) (a : real) :=
∀ x : real, x ∈ S → x ≤ a

def is_least (S : myset real) (a : real) :=
a ∈ S ∧ ∀ x : real, x ∈ S → a ≤ x

def upper_bounds (S : myset real) : myset real :=
λ x, is_upper_bound S x

def is_least_upper_bound (S : myset real) (a : real) :=
is_least (upper_bounds S) a

def bounded_above (S : myset real) :=
∃ a : real, is_upper_bound S a

theorem least_upper_bound_property (S : myset real) :
bounded_above S → ∃ x : real, is_least_upper_bound S x :=
sorry

open classical

noncomputable def sup (S : myset real) (h : bounded_above S) :=
some (least_upper_bound_property S h)

variables {S : myset real} (h : bounded_above S)

theorem sup_is_ub : is_upper_bound S (sup S h) := sorry

theorem sup_is_lub : is_least_upper_bound S (sup S h) := sorry

end hidden
