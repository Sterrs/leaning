λ (m n : mynat),
  mynat.rec
    (eq.rec true.intro
       (eq.rec (eq.refl (m = add zero m))
          (eq.rec
             (eq.rec (eq.refl (m = add zero m))
                (eq.rec (eq.refl (add zero m))
                   (mynat.rec (eq.refl zero)
                      (λ (m_n : mynat) (m_ih : add zero m_n = m_n),
                         eq.rec m_ih
                           (eq.rec (eq.refl (succ (add zero m_n) = succ m_n))
                              (eq.rec (eq.refl (succ (add zero m_n) = succ m_n))
                                 (propext
                                    {mp := λ (h : succ (add zero m_n) = succ m_n),
                                             eq.rec
                                               (λ (h11 : succ (add zero m_n) = succ (add zero m_n))
                                                (a : add zero m_n = add zero m_n → add zero m_n = m_n),
                                                  a (eq.refl (add zero m_n)))
                                               h
                                               h
                                               (λ (n_eq : add zero m_n = m_n), n_eq),
                                     mpr := λ (a : add zero m_n = m_n), eq.rec (eq.refl (succ (add zero m_n))) a}))))
                      m)))
             (propext {mp := λ (hl : m = m), true.intro, mpr := λ (hr : true), eq.refl m}))))
    (λ (n_n : mynat) (n_ih : add m n_n = add n_n m),
       eq.rec n_ih
         (eq.rec (eq.refl (succ (add m n_n) = add (succ n_n) m))
            (eq.rec
               (eq.rec (eq.refl (succ (add m n_n) = add (succ n_n) m))
                  (mynat.rec (eq.refl (succ n_n))
                     (λ (n_n_1 : mynat) (n_ih : add (succ n_n) n_n_1 = succ (add n_n n_n_1)),
                        eq.rec n_ih
                          (eq.rec (eq.refl (succ (add (succ n_n) n_n_1) = succ (succ (add n_n n_n_1))))
                             (eq.rec (eq.refl (succ (add (succ n_n) n_n_1) = succ (succ (add n_n n_n_1))))
                                (propext
                                   {mp := λ (h : succ (add (succ n_n) n_n_1) = succ (succ (add n_n n_n_1))),
                                            eq.rec
                                              (λ (h11 : succ (add (succ n_n) n_n_1) = succ (add (succ n_n) n_n_1))
                                               (a :
                                                 add (succ n_n) n_n_1 = add (succ n_n) n_n_1 →
                                                 add (succ n_n) n_n_1 = succ (add n_n n_n_1)),
                                                 a (eq.refl (add (succ n_n) n_n_1)))
                                              h
                                              h
                                              (λ (n_eq : add (succ n_n) n_n_1 = succ (add n_n n_n_1)), n_eq),
                                    mpr := λ (a : add (succ n_n) n_n_1 = succ (add n_n n_n_1)),
                                             eq.rec (eq.refl (succ (add (succ n_n) n_n_1))) a}))))
                     m))
               (propext
                  {mp := λ (h : succ (add m n_n) = succ (add n_n m)),
                           eq.rec
                             (λ (h11 : succ (add m n_n) = succ (add m n_n))
                              (a : add m n_n = add m n_n → add m n_n = add n_n m), a (eq.refl (add m n_n)))
                             h
                             h
                             (λ (n_eq : add m n_n = add n_n m), n_eq),
                   mpr := λ (a : add m n_n = add n_n m), eq.rec (eq.refl (succ (add m n_n))) a}))))
    n
