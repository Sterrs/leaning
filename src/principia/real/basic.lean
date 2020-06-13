import .cau_seq

namespace hidden


def real := quotient cau_seq.real_setoid

namespace real

private lemma class_setoid (f g : cau_seq) :
⟦f⟧ = ⟦g⟧ ↔ f ≈ g := iff.intro quotient.exact quotient.sound

theorem class_equiv {f g : cau_seq} :
⟦f⟧ = ⟦g⟧ ↔ cau_seq.equivalent f g  :=
begin
  split; assume h,
    rwa [←cau_seq.setoid_equiv, ←class_setoid],
  rwa [class_setoid, cau_seq.setoid_equiv],
end

end real

end hidden
