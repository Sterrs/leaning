λ (m n : mynat),
  mynat.rec
    (eq.rec (eq.refl m)
       (eq.rec (eq.refl (m = add zero m))
          (eq.rec (eq.refl (m = add zero m))
             (mynat.rec (eq.refl zero)
                (λ (m_n : mynat) (m_ih : add zero m_n = m_n),
                   eq.rec (eq.refl (succ m_n))
                     (eq.rec (eq.refl (succ (add zero m_n) = succ m_n))
                        (eq.rec (eq.refl (succ (add zero m_n) = succ m_n)) m_ih)))
                m))))
    (λ (n_n : mynat) (n_ih : add m n_n = add n_n m),
       eq.rec
         (eq.rec (eq.refl (succ (add n_n m)))
            (eq.rec (eq.refl (succ (add m n_n) = succ (add n_n m)))
               (eq.rec (eq.refl (succ (add m n_n) = succ (add n_n m))) n_ih)))
         (eq.rec (eq.refl (succ (add m n_n) = add (succ n_n) m))
            (eq.rec (eq.refl (succ (add m n_n) = add (succ n_n) m))
               (mynat.rec (eq.refl (succ n_n))
                  (λ (n_n_1 : mynat) (n_ih : add (succ n_n) n_n_1 = succ (add n_n n_n_1)),
                     eq.rec (eq.refl (succ (succ (add n_n n_n_1))))
                       (eq.rec (eq.refl (succ (add (succ n_n) n_n_1) = succ (succ (add n_n n_n_1))))
                          (eq.rec (eq.refl (succ (add (succ n_n) n_n_1) = succ (succ (add n_n n_n_1)))) n_ih)))
                  m))))
    n
