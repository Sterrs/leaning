λ (m n : mynat),
  (mynat.rec
     ⟨λ (m : mynat),
        eq.rec (eq.refl m)
          (eq.rec (eq.refl (m = add zero m))
             (eq.rec (eq.refl (m = add zero m))
                ((mynat.rec ⟨eq.refl zero, punit.star⟩
                    (λ (n : mynat)
                     (ih :
                       pprod (add zero n = n)
                         (mynat.rec punit (λ (n : mynat) (ih : Type), pprod (pprod (add zero n = n) ih) punit) n)),
                       ⟨eq.rec (eq.refl (succ n))
                          (eq.rec (eq.refl (succ (add zero n) = succ n))
                             (eq.rec (eq.refl (succ (add zero n) = succ n)) (ih.fst))),
                        ⟨ih, punit.star⟩⟩)
                    m).fst))),
      punit.star⟩
     (λ (n : mynat)
      (ih :
        pprod (∀ (m : mynat), add m n = add n m)
          (mynat.rec punit (λ (n : mynat) (ih : Type), pprod (pprod (∀ (m : mynat), add m n = add n m) ih) punit)
             n)),
        ⟨λ (m : mynat),
           eq.rec
             (eq.rec (eq.refl (succ (add n m)))
                (eq.rec (eq.refl (succ (add m n) = succ (add n m)))
                   (eq.rec (eq.refl (succ (add m n) = succ (add n m))) (ih.fst m))))
             (eq.rec (eq.refl (succ (add m n) = add (succ n) m))
                (eq.rec (eq.refl (succ (add m n) = add (succ n) m))
                   ((mynat.rec ⟨λ (m : mynat), eq.refl (succ m), punit.star⟩
                       (λ (n : mynat)
                        (ih :
                          pprod (∀ (m : mynat), add (succ m) n = succ (add m n))
                            (mynat.rec punit
                               (λ (n : mynat) (ih : Type),
                                  pprod (pprod (∀ (m : mynat), add (succ m) n = succ (add m n)) ih) punit)
                               n)),
                          ⟨λ (m : mynat),
                             eq.rec (eq.refl (succ (succ (add m n))))
                               (eq.rec (eq.refl (succ (add (succ m) n) = succ (succ (add m n))))
                                  (eq.rec (eq.refl (succ (add (succ m) n) = succ (succ (add m n)))) (ih.fst m))),
                           ⟨ih, punit.star⟩⟩)
                       m).fst
                      n))),
         ⟨ih, punit.star⟩⟩)
     n).fst
    m
