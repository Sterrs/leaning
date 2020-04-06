λ (m n k : mynat) (hmnz : m = zero → false),
  or.rec
    (λ (h : ∃ (k_1 : mynat), k = add n k_1)
     («_» : (∃ (k_1 : mynat), k = add n k_1) ∨ ∃ (k_1 : mynat), n = add k k_1) (hmnmk : mul m n = mul m k),
       Exists.rec
         (λ (w : mynat) (h : k = add n w) («_» : ∃ (k_1 : mynat), k = add n k_1),
            eq.rec true.intro
              (eq.rec (eq.refl (n = k))
                 (eq.rec
                    (eq.rec (eq.refl (n = k))
                       (eq.rec h
                          (eq.rec (eq.refl (add n w))
                             (mynat.rec
                                (λ (hmn0 : zero = zero),
                                   eq.rec true.intro
                                     (eq.rec (eq.refl (zero = zero))
                                        (eq.rec (eq.refl (zero = zero))
                                           (propext
                                              {mp := λ (hl : zero = zero), true.intro,
                                               mpr := λ (hr : true), eq.refl zero}))))
                                (λ (n : mynat) (ih : mul m n = zero → n = zero) (hmn0 : add m (mul m n) = zero),
                                   false.rec (succ n = zero)
                                     (hmnz
                                        (mynat.rec
                                           (eq.rec true.intro
                                              (eq.rec (eq.refl (add zero (mul m n) = zero → zero = zero))
                                                 (eq.rec
                                                    (propext
                                                       {mp := λ (hab : add zero (mul m n) = zero → zero = zero)
                                                              (hc : mul m n = zero),
                                                                (eq.rec
                                                                   {mp := λ (h : zero = zero), h,
                                                                    mpr := λ (h : zero = zero), h}
                                                                   (eq.rec (eq.refl (zero = zero))
                                                                      (propext
                                                                         {mp := λ (hl : zero = zero), true.intro,
                                                                          mpr := λ (hr : true), eq.refl zero}))).mp
                                                                  (hab
                                                                     ((eq.rec
                                                                         {mp := λ (h : add zero (mul m n) = zero), h,
                                                                          mpr := λ (h : add zero (mul m n) = zero), h}
                                                                         (eq.rec (eq.refl (add zero (mul m n) = zero))
                                                                            (eq.rec (eq.refl (eq (add zero (mul m n))))
                                                                               (eq.rec (eq.refl (add zero (mul m n)))
                                                                                  (mynat.rec
                                                                                     (eq.rec true.intro
                                                                                        (eq.rec (eq.refl (zero = zero))
                                                                                           (eq.rec
                                                                                              (eq.refl (zero = zero))
                                                                                              (propext
                                                                                                 {mp := λ
                                                                                                        (hl :
                                                                                                          zero = zero),
                                                                                                          true.intro,
                                                                                                  mpr := λ (hr : true),
                                                                                                           eq.refl
                                                                                                             zero}))))
                                                                                     (λ (n_n : mynat)
                                                                                      (n_ih : add zero n_n = n_n),
                                                                                        eq.rec n_ih
                                                                                          (eq.rec
                                                                                             (eq.refl
                                                                                                (succ (add zero n_n) =
                                                                                                   succ n_n))
                                                                                             (eq.rec
                                                                                                (eq.refl
                                                                                                   (succ
                                                                                                        (add zero n_n) =
                                                                                                      succ n_n))
                                                                                                (propext
                                                                                                   {mp := λ
                                                                                                          (h :
                                                                                                            succ
                                                                                                                (add
                                                                                                                   zero
                                                                                                                   n_n) =
                                                                                                              succ n_n),
                                                                                                            eq.rec
                                                                                                              (λ
                                                                                                               (h11 :
                                                                                                                 succ
                                                                                                                     (add
                                                                                                                        zero
                                                                                                                        n_n) =
                                                                                                                   succ
                                                                                                                     (add
                                                                                                                        zero
                                                                                                                        n_n))
                                                                                                               (a :
                                                                                                                 add
                                                                                                                     zero
                                                                                                                     n_n =
                                                                                                                   add
                                                                                                                     zero
                                                                                                                     n_n →
                                                                                                                 add
                                                                                                                     zero
                                                                                                                     n_n =
                                                                                                                   n_n),
                                                                                                                 a
                                                                                                                   (eq.refl
                                                                                                                      (add
                                                                                                                         zero
                                                                                                                         n_n)))
                                                                                                              h
                                                                                                              h
                                                                                                              (λ
                                                                                                               (n_eq :
                                                                                                                 add
                                                                                                                     zero
                                                                                                                     n_n =
                                                                                                                   n_n),
                                                                                                                 n_eq),
                                                                                                    mpr := λ
                                                                                                           (a :
                                                                                                             add zero
                                                                                                                 n_n =
                                                                                                               n_n),
                                                                                                             eq.rec
                                                                                                               (eq.refl
                                                                                                                  (succ
                                                                                                                     (add
                                                                                                                        zero
                                                                                                                        n_n)))
                                                                                                               a}))))
                                                                                     (mul m n)))))).mpr
                                                                        hc)),
                                                        mpr := λ (hcd : mul m n = zero → true)
                                                               (ha : add zero (mul m n) = zero),
                                                                 (eq.rec
                                                                    {mp := λ (h : zero = zero), h,
                                                                     mpr := λ (h : zero = zero), h}
                                                                    (eq.rec (eq.refl (zero = zero))
                                                                       (propext
                                                                          {mp := λ (hl : zero = zero), true.intro,
                                                                           mpr := λ (hr : true), eq.refl zero}))).mpr
                                                                   (hcd
                                                                      ((eq.rec
                                                                          {mp := λ (h : add zero (mul m n) = zero), h,
                                                                           mpr := λ (h : add zero (mul m n) = zero), h}
                                                                          (eq.rec (eq.refl (add zero (mul m n) = zero))
                                                                             (eq.rec (eq.refl (eq (add zero (mul m n))))
                                                                                (eq.rec (eq.refl (add zero (mul m n)))
                                                                                   (mynat.rec
                                                                                      (eq.rec true.intro
                                                                                         (eq.rec (eq.refl (zero = zero))
                                                                                            (eq.rec
                                                                                               (eq.refl (zero = zero))
                                                                                               (propext
                                                                                                  {mp := λ
                                                                                                         (hl :
                                                                                                           zero = zero),
                                                                                                           true.intro,
                                                                                                   mpr := λ
                                                                                                          (hr : true),
                                                                                                            eq.refl
                                                                                                              zero}))))
                                                                                      (λ (n_n : mynat)
                                                                                       (n_ih : add zero n_n = n_n),
                                                                                         eq.rec n_ih
                                                                                           (eq.rec
                                                                                              (eq.refl
                                                                                                 (succ (add zero n_n) =
                                                                                                    succ n_n))
                                                                                              (eq.rec
                                                                                                 (eq.refl
                                                                                                    (succ
                                                                                                         (add zero
                                                                                                            n_n) =
                                                                                                       succ n_n))
                                                                                                 (propext
                                                                                                    {mp := λ
                                                                                                           (h :
                                                                                                             succ
                                                                                                                 (add
                                                                                                                    zero
                                                                                                                    n_n) =
                                                                                                               succ
                                                                                                                 n_n),
                                                                                                             eq.rec
                                                                                                               (λ
                                                                                                                (h11 :
                                                                                                                  succ
                                                                                                                      (add
                                                                                                                         zero
                                                                                                                         n_n) =
                                                                                                                    succ
                                                                                                                      (add
                                                                                                                         zero
                                                                                                                         n_n))
                                                                                                                (a :
                                                                                                                  add
                                                                                                                      zero
                                                                                                                      n_n =
                                                                                                                    add
                                                                                                                      zero
                                                                                                                      n_n →
                                                                                                                  add
                                                                                                                      zero
                                                                                                                      n_n =
                                                                                                                    n_n),
                                                                                                                  a
                                                                                                                    (eq.refl
                                                                                                                       (add
                                                                                                                          zero
                                                                                                                          n_n)))
                                                                                                               h
                                                                                                               h
                                                                                                               (λ
                                                                                                                (n_eq :
                                                                                                                  add
                                                                                                                      zero
                                                                                                                      n_n =
                                                                                                                    n_n),
                                                                                                                  n_eq),
                                                                                                     mpr := λ
                                                                                                            (a :
                                                                                                              add zero
                                                                                                                  n_n =
                                                                                                                n_n),
                                                                                                              eq.rec
                                                                                                                (eq.refl
                                                                                                                   (succ
                                                                                                                      (add
                                                                                                                         zero
                                                                                                                         n_n)))
                                                                                                                a}))))
                                                                                      (mul m n)))))).mp
                                                                         ha))})
                                                    (propext
                                                       {mp := λ (h : mul m n = zero → true), true.intro,
                                                        mpr := λ (ha : true) (h : mul m n = zero), true.intro}))))
                                           (λ (n_1 : mynat) (ih : add n_1 (mul m n) = zero → n_1 = zero),
                                              eq.rec
                                                (λ (hsmnz : succ (add (mul m n) n_1) = zero),
                                                   false.rec (succ n_1 = zero)
                                                     (eq.rec
                                                        (λ
                                                         («_» : succ (add (mul m n) n_1) = succ (add (mul m n) n_1))
                                                         (a : zero = succ (add (mul m n) n_1)),
                                                           eq.rec
                                                             (λ (h11 : zero = zero)
                                                              (a :
                                                                hsmnz == eq.refl (succ (add (mul m n) n_1)) → false),
                                                                a)
                                                             a
                                                             a)
                                                        hsmnz
                                                        hsmnz
                                                        (eq.refl zero)
                                                        (heq.refl hsmnz)))
                                                (eq.rec (eq.refl (add (succ n_1) (mul m n) = zero → succ n_1 = zero))
                                                   (propext
                                                      {mp := λ
                                                             (hab : add (succ n_1) (mul m n) = zero → succ n_1 = zero)
                                                             (hc : succ (add (mul m n) n_1) = zero),
                                                               hab
                                                                 ((eq.rec
                                                                     {mp := λ (h : add (succ n_1) (mul m n) = zero), h,
                                                                      mpr := λ (h : add (succ n_1) (mul m n) = zero),
                                                                               h}
                                                                     (eq.rec (eq.refl (add (succ n_1) (mul m n) = zero))
                                                                        (eq.rec
                                                                           (eq.refl (eq (add (succ n_1) (mul m n))))
                                                                           (mynat.rec
                                                                              (eq.rec true.intro
                                                                                 (eq.rec
                                                                                    (eq.refl
                                                                                       (succ n_1 = succ (add zero n_1)))
                                                                                    (eq.rec
                                                                                       (eq.rec
                                                                                          (eq.refl
                                                                                             (succ n_1 =
                                                                                                succ (add zero n_1)))
                                                                                          (eq.rec
                                                                                             (eq.refl
                                                                                                (succ (add zero n_1)))
                                                                                             (eq.rec
                                                                                                (mynat.rec
                                                                                                   (eq.refl zero)
                                                                                                   (λ (m_n : mynat)
                                                                                                    (m_ih :
                                                                                                      add zero m_n =
                                                                                                        m_n),
                                                                                                      eq.rec m_ih
                                                                                                        (eq.rec
                                                                                                           (eq.refl
                                                                                                              (succ
                                                                                                                   (add
                                                                                                                      zero
                                                                                                                      m_n) =
                                                                                                                 succ
                                                                                                                   m_n))
                                                                                                           (eq.rec
                                                                                                              (eq.refl
                                                                                                                 (succ
                                                                                                                      (add
                                                                                                                         zero
                                                                                                                         m_n) =
                                                                                                                    succ
                                                                                                                      m_n))
                                                                                                              (propext
                                                                                                                 {mp := λ
                                                                                                                        (h :
                                                                                                                          succ
                                                                                                                              (add
                                                                                                                                 zero
                                                                                                                                 m_n) =
                                                                                                                            succ
                                                                                                                              m_n),
                                                                                                                          eq.rec
                                                                                                                            (λ
                                                                                                                             (h11 :
                                                                                                                               … =
                                                                                                                                 …)
                                                                                                                             (a :
                                                                                                                               … →
                                                                                                                               …),
                                                                                                                               a
                                                                                                                                 …)
                                                                                                                            h
                                                                                                                            h
                                                                                                                            (λ
                                                                                                                             (n_eq :
                                                                                                                               add
                                                                                                                                   zero
                                                                                                                                   m_n =
                                                                                                                                 m_n),
                                                                                                                               n_eq),
                                                                                                                  mpr := λ
                                                                                                                         (a :
                                                                                                                           add
                                                                                                                               zero
                                                                                                                               m_n =
                                                                                                                             m_n),
                                                                                                                           eq.rec
                                                                                                                             (eq.refl
                                                                                                                                (succ
                                                                                                                                   (add
                                                                                                                                      zero
                                                                                                                                      m_n)))
                                                                                                                             a}))))
                                                                                                   n_1)
                                                                                                (eq.rec
                                                                                                   (eq.refl
                                                                                                      (succ
                                                                                                           (add zero
                                                                                                              n_1) =
                                                                                                         succ n_1))
                                                                                                   (eq.rec
                                                                                                      (eq.refl
                                                                                                         (succ
                                                                                                              (add zero
                                                                                                                 n_1) =
                                                                                                            succ n_1))
                                                                                                      (propext
                                                                                                         {mp := λ
                                                                                                                (h :
                                                                                                                  succ
                                                                                                                      (add
                                                                                                                         zero
                                                                                                                         n_1) =
                                                                                                                    succ
                                                                                                                      n_1),
                                                                                                                  eq.rec
                                                                                                                    (λ
                                                                                                                     (h11 :
                                                                                                                       succ
                                                                                                                           (add
                                                                                                                              zero
                                                                                                                              n_1) =
                                                                                                                         succ
                                                                                                                           (add
                                                                                                                              zero
                                                                                                                              n_1))
                                                                                                                     (a :
                                                                                                                       add
                                                                                                                           zero
                                                                                                                           n_1 =
                                                                                                                         add
                                                                                                                           zero
                                                                                                                           n_1 →
                                                                                                                       add
                                                                                                                           zero
                                                                                                                           n_1 =
                                                                                                                         n_1),
                                                                                                                       a
                                                                                                                         (eq.refl
                                                                                                                            (add
                                                                                                                               zero
                                                                                                                               n_1)))
                                                                                                                    h
                                                                                                                    h
                                                                                                                    (λ
                                                                                                                     (n_eq :
                                                                                                                       add
                                                                                                                           zero
                                                                                                                           n_1 =
                                                                                                                         n_1),
                                                                                                                       n_eq),
                                                                                                          mpr := λ
                                                                                                                 (a :
                                                                                                                   add
                                                                                                                       zero
                                                                                                                       n_1 =
                                                                                                                     n_1),
                                                                                                                   eq.rec
                                                                                                                     (eq.refl
                                                                                                                        (succ
                                                                                                                           (add
                                                                                                                              zero
                                                                                                                              n_1)))
                                                                                                                     a}))))))
                                                                                       (propext
                                                                                          {mp := λ
                                                                                                 (hl :
                                                                                                   succ n_1 = succ n_1),
                                                                                                   true.intro,
                                                                                           mpr := λ (hr : true),
                                                                                                    eq.refl
                                                                                                      (succ n_1)}))))
                                                                              (λ (n_n : mynat)
                                                                               (n_ih :
                                                                                 add (succ n_1) n_n =
                                                                                   succ (add n_n n_1)),
                                                                                 eq.rec n_ih
                                                                                   (eq.rec
                                                                                      (eq.refl
                                                                                         (succ (add (succ n_1) n_n) =
                                                                                            succ (add (succ n_n) n_1)))
                                                                                      (eq.rec
                                                                                         (eq.rec
                                                                                            (eq.refl
                                                                                               (succ
                                                                                                    (add (succ n_1)
                                                                                                       n_n) =
                                                                                                  succ
                                                                                                    (add (succ n_n)
                                                                                                       n_1)))
                                                                                            (eq.rec
                                                                                               (mynat.rec
                                                                                                  (eq.refl (succ n_n))
                                                                                                  (λ (n_n_1 : mynat)
                                                                                                   (n_ih :
                                                                                                     add (succ n_n)
                                                                                                         n_n_1 =
                                                                                                       succ
                                                                                                         (add n_n
                                                                                                            n_n_1)),
                                                                                                     eq.rec n_ih
                                                                                                       (eq.rec
                                                                                                          (eq.refl
                                                                                                             (succ
                                                                                                                  (add
                                                                                                                     (succ
                                                                                                                        n_n)
                                                                                                                     n_n_1) =
                                                                                                                succ
                                                                                                                  (succ
                                                                                                                     (add
                                                                                                                        n_n
                                                                                                                        n_n_1))))
                                                                                                          (eq.rec
                                                                                                             (eq.refl
                                                                                                                (succ
                                                                                                                     (add
                                                                                                                        (succ
                                                                                                                           n_n)
                                                                                                                        n_n_1) =
                                                                                                                   succ
                                                                                                                     (succ
                                                                                                                        (add
                                                                                                                           n_n
                                                                                                                           n_n_1))))
                                                                                                             (propext
                                                                                                                {mp := λ
                                                                                                                       (h :
                                                                                                                         succ
                                                                                                                             (add
                                                                                                                                (succ
                                                                                                                                   n_n)
                                                                                                                                n_n_1) =
                                                                                                                           succ
                                                                                                                             (succ
                                                                                                                                (add
                                                                                                                                   n_n
                                                                                                                                   n_n_1))),
                                                                                                                         eq.rec
                                                                                                                           (λ
                                                                                                                            (h11 :
                                                                                                                              succ
                                                                                                                                  … =
                                                                                                                                succ
                                                                                                                                  …)
                                                                                                                            (a :
                                                                                                                              … =
                                                                                                                                … →
                                                                                                                              … =
                                                                                                                                …),
                                                                                                                              a
                                                                                                                                (eq.refl
                                                                                                                                   …))
                                                                                                                           h
                                                                                                                           h
                                                                                                                           (λ
                                                                                                                            (n_eq :
                                                                                                                              add
                                                                                                                                  (succ
                                                                                                                                     n_n)
                                                                                                                                  n_n_1 =
                                                                                                                                succ
                                                                                                                                  (add
                                                                                                                                     n_n
                                                                                                                                     n_n_1)),
                                                                                                                              n_eq),
                                                                                                                 mpr := λ
                                                                                                                        (a :
                                                                                                                          add
                                                                                                                              (succ
                                                                                                                                 n_n)
                                                                                                                              n_n_1 =
                                                                                                                            succ
                                                                                                                              (add
                                                                                                                                 n_n
                                                                                                                                 n_n_1)),
                                                                                                                          eq.rec
                                                                                                                            (eq.refl
                                                                                                                               (succ
                                                                                                                                  (add
                                                                                                                                     (succ
                                                                                                                                        n_n)
                                                                                                                                     n_n_1)))
                                                                                                                            a}))))
                                                                                                  n_1)
                                                                                               (eq.rec
                                                                                                  (eq.refl
                                                                                                     (succ
                                                                                                          (add
                                                                                                             (succ n_n)
                                                                                                             n_1) =
                                                                                                        succ
                                                                                                          (succ
                                                                                                             (add n_n
                                                                                                                n_1))))
                                                                                                  (eq.rec
                                                                                                     (eq.refl
                                                                                                        (succ
                                                                                                             (add
                                                                                                                (succ
                                                                                                                   n_n)
                                                                                                                n_1) =
                                                                                                           succ
                                                                                                             (succ
                                                                                                                (add n_n
                                                                                                                   n_1))))
                                                                                                     (propext
                                                                                                        {mp := λ
                                                                                                               (h :
                                                                                                                 succ
                                                                                                                     (add
                                                                                                                        (succ
                                                                                                                           n_n)
                                                                                                                        n_1) =
                                                                                                                   succ
                                                                                                                     (succ
                                                                                                                        (add
                                                                                                                           n_n
                                                                                                                           n_1))),
                                                                                                                 eq.rec
                                                                                                                   (λ
                                                                                                                    (h11 :
                                                                                                                      succ
                                                                                                                          (add
                                                                                                                             (succ
                                                                                                                                n_n)
                                                                                                                             n_1) =
                                                                                                                        succ
                                                                                                                          (add
                                                                                                                             (succ
                                                                                                                                n_n)
                                                                                                                             n_1))
                                                                                                                    (a :
                                                                                                                      add
                                                                                                                          (succ
                                                                                                                             n_n)
                                                                                                                          n_1 =
                                                                                                                        add
                                                                                                                          (succ
                                                                                                                             n_n)
                                                                                                                          n_1 →
                                                                                                                      add
                                                                                                                          (succ
                                                                                                                             n_n)
                                                                                                                          n_1 =
                                                                                                                        succ
                                                                                                                          (add
                                                                                                                             n_n
                                                                                                                             n_1)),
                                                                                                                      a
                                                                                                                        (eq.refl
                                                                                                                           (add
                                                                                                                              (succ
                                                                                                                                 n_n)
                                                                                                                              n_1)))
                                                                                                                   h
                                                                                                                   h
                                                                                                                   (λ
                                                                                                                    (n_eq :
                                                                                                                      add
                                                                                                                          (succ
                                                                                                                             n_n)
                                                                                                                          n_1 =
                                                                                                                        succ
                                                                                                                          (add
                                                                                                                             n_n
                                                                                                                             n_1)),
                                                                                                                      n_eq),
                                                                                                         mpr := λ
                                                                                                                (a :
                                                                                                                  add
                                                                                                                      (succ
                                                                                                                         n_n)
                                                                                                                      n_1 =
                                                                                                                    succ
                                                                                                                      (add
                                                                                                                         n_n
                                                                                                                         n_1)),
                                                                                                                  eq.rec
                                                                                                                    (eq.refl
                                                                                                                       (succ
                                                                                                                          (add
                                                                                                                             (succ
                                                                                                                                n_n)
                                                                                                                             n_1)))
                                                                                                                    a})))))
                                                                                         (propext
                                                                                            {mp := λ
                                                                                                   (h :
                                                                                                     succ
                                                                                                         (add (succ n_1)
                                                                                                            n_n) =
                                                                                                       succ
                                                                                                         (succ
                                                                                                            (add n_n
                                                                                                               n_1))),
                                                                                                     eq.rec
                                                                                                       (λ
                                                                                                        (h11 :
                                                                                                          succ
                                                                                                              (add
                                                                                                                 (succ
                                                                                                                    n_1)
                                                                                                                 n_n) =
                                                                                                            succ
                                                                                                              (add
                                                                                                                 (succ
                                                                                                                    n_1)
                                                                                                                 n_n))
                                                                                                        (a :
                                                                                                          add (succ n_1)
                                                                                                              n_n =
                                                                                                            add
                                                                                                              (succ n_1)
                                                                                                              n_n →
                                                                                                          add (succ n_1)
                                                                                                              n_n =
                                                                                                            succ
                                                                                                              (add n_n
                                                                                                                 n_1)),
                                                                                                          a
                                                                                                            (eq.refl
                                                                                                               (add
                                                                                                                  (succ
                                                                                                                     n_1)
                                                                                                                  n_n)))
                                                                                                       h
                                                                                                       h
                                                                                                       (λ
                                                                                                        (n_eq :
                                                                                                          add (succ n_1)
                                                                                                              n_n =
                                                                                                            succ
                                                                                                              (add n_n
                                                                                                                 n_1)),
                                                                                                          n_eq),
                                                                                             mpr := λ
                                                                                                    (a :
                                                                                                      add (succ n_1)
                                                                                                          n_n =
                                                                                                        succ
                                                                                                          (add n_n
                                                                                                             n_1)),
                                                                                                      eq.rec
                                                                                                        (eq.refl
                                                                                                           (succ
                                                                                                              (add
                                                                                                                 (succ
                                                                                                                    n_1)
                                                                                                                 n_n)))
                                                                                                        a}))))
                                                                              (mul m n))))).mpr
                                                                    hc),
                                                       mpr := λ
                                                              (hcd :
                                                                succ (add (mul m n) n_1) = zero → succ n_1 = zero)
                                                              (ha : add (succ n_1) (mul m n) = zero),
                                                                hcd
                                                                  ((eq.rec
                                                                      {mp := λ (h : add (succ n_1) (mul m n) = zero),
                                                                               h,
                                                                       mpr := λ (h : add (succ n_1) (mul m n) = zero),
                                                                                h}
                                                                      (eq.rec
                                                                         (eq.refl (add (succ n_1) (mul m n) = zero))
                                                                         (eq.rec
                                                                            (eq.refl (eq (add (succ n_1) (mul m n))))
                                                                            (mynat.rec
                                                                               (eq.rec true.intro
                                                                                  (eq.rec
                                                                                     (eq.refl
                                                                                        (succ n_1 =
                                                                                           succ (add zero n_1)))
                                                                                     (eq.rec
                                                                                        (eq.rec
                                                                                           (eq.refl
                                                                                              (succ n_1 =
                                                                                                 succ (add zero n_1)))
                                                                                           (eq.rec
                                                                                              (eq.refl
                                                                                                 (succ (add zero n_1)))
                                                                                              (eq.rec
                                                                                                 (mynat.rec
                                                                                                    (eq.refl zero)
                                                                                                    (λ (m_n : mynat)
                                                                                                     (m_ih :
                                                                                                       add zero m_n =
                                                                                                         m_n),
                                                                                                       eq.rec m_ih
                                                                                                         (eq.rec
                                                                                                            (eq.refl
                                                                                                               (succ
                                                                                                                    (add
                                                                                                                       zero
                                                                                                                       m_n) =
                                                                                                                  succ
                                                                                                                    m_n))
                                                                                                            (eq.rec
                                                                                                               (eq.refl
                                                                                                                  (succ
                                                                                                                       (add
                                                                                                                          zero
                                                                                                                          m_n) =
                                                                                                                     succ
                                                                                                                       m_n))
                                                                                                               (propext
                                                                                                                  {mp := λ
                                                                                                                         (h :
                                                                                                                           succ
                                                                                                                               (add
                                                                                                                                  zero
                                                                                                                                  m_n) =
                                                                                                                             succ
                                                                                                                               m_n),
                                                                                                                           eq.rec
                                                                                                                             (λ
                                                                                                                              (h11 :
                                                                                                                                … =
                                                                                                                                  …)
                                                                                                                              (a :
                                                                                                                                … →
                                                                                                                                …),
                                                                                                                                a
                                                                                                                                  …)
                                                                                                                             h
                                                                                                                             h
                                                                                                                             (λ
                                                                                                                              (n_eq :
                                                                                                                                add
                                                                                                                                    zero
                                                                                                                                    m_n =
                                                                                                                                  m_n),
                                                                                                                                n_eq),
                                                                                                                   mpr := λ
                                                                                                                          (a :
                                                                                                                            add
                                                                                                                                zero
                                                                                                                                m_n =
                                                                                                                              m_n),
                                                                                                                            eq.rec
                                                                                                                              (eq.refl
                                                                                                                                 (succ
                                                                                                                                    (add
                                                                                                                                       zero
                                                                                                                                       m_n)))
                                                                                                                              a}))))
                                                                                                    n_1)
                                                                                                 (eq.rec
                                                                                                    (eq.refl
                                                                                                       (succ
                                                                                                            (add zero
                                                                                                               n_1) =
                                                                                                          succ n_1))
                                                                                                    (eq.rec
                                                                                                       (eq.refl
                                                                                                          (succ
                                                                                                               (add zero
                                                                                                                  n_1) =
                                                                                                             succ n_1))
                                                                                                       (propext
                                                                                                          {mp := λ
                                                                                                                 (h :
                                                                                                                   succ
                                                                                                                       (add
                                                                                                                          zero
                                                                                                                          n_1) =
                                                                                                                     succ
                                                                                                                       n_1),
                                                                                                                   eq.rec
                                                                                                                     (λ
                                                                                                                      (h11 :
                                                                                                                        succ
                                                                                                                            (add
                                                                                                                               zero
                                                                                                                               n_1) =
                                                                                                                          succ
                                                                                                                            (add
                                                                                                                               zero
                                                                                                                               n_1))
                                                                                                                      (a :
                                                                                                                        add
                                                                                                                            zero
                                                                                                                            n_1 =
                                                                                                                          add
                                                                                                                            zero
                                                                                                                            n_1 →
                                                                                                                        add
                                                                                                                            zero
                                                                                                                            n_1 =
                                                                                                                          n_1),
                                                                                                                        a
                                                                                                                          (eq.refl
                                                                                                                             (add
                                                                                                                                zero
                                                                                                                                n_1)))
                                                                                                                     h
                                                                                                                     h
                                                                                                                     (λ
                                                                                                                      (n_eq :
                                                                                                                        add
                                                                                                                            zero
                                                                                                                            n_1 =
                                                                                                                          n_1),
                                                                                                                        n_eq),
                                                                                                           mpr := λ
                                                                                                                  (a :
                                                                                                                    add
                                                                                                                        zero
                                                                                                                        n_1 =
                                                                                                                      n_1),
                                                                                                                    eq.rec
                                                                                                                      (eq.refl
                                                                                                                         (succ
                                                                                                                            (add
                                                                                                                               zero
                                                                                                                               n_1)))
                                                                                                                      a}))))))
                                                                                        (propext
                                                                                           {mp := λ
                                                                                                  (hl :
                                                                                                    succ n_1 =
                                                                                                      succ n_1),
                                                                                                    true.intro,
                                                                                            mpr := λ (hr : true),
                                                                                                     eq.refl
                                                                                                       (succ n_1)}))))
                                                                               (λ (n_n : mynat)
                                                                                (n_ih :
                                                                                  add (succ n_1) n_n =
                                                                                    succ (add n_n n_1)),
                                                                                  eq.rec n_ih
                                                                                    (eq.rec
                                                                                       (eq.refl
                                                                                          (succ (add (succ n_1) n_n) =
                                                                                             succ (add (succ n_n) n_1)))
                                                                                       (eq.rec
                                                                                          (eq.rec
                                                                                             (eq.refl
                                                                                                (succ
                                                                                                     (add (succ n_1)
                                                                                                        n_n) =
                                                                                                   succ
                                                                                                     (add (succ n_n)
                                                                                                        n_1)))
                                                                                             (eq.rec
                                                                                                (mynat.rec
                                                                                                   (eq.refl (succ n_n))
                                                                                                   (λ (n_n_1 : mynat)
                                                                                                    (n_ih :
                                                                                                      add (succ n_n)
                                                                                                          n_n_1 =
                                                                                                        succ
                                                                                                          (add n_n
                                                                                                             n_n_1)),
                                                                                                      eq.rec n_ih
                                                                                                        (eq.rec
                                                                                                           (eq.refl
                                                                                                              (succ
                                                                                                                   (add
                                                                                                                      (succ
                                                                                                                         n_n)
                                                                                                                      n_n_1) =
                                                                                                                 succ
                                                                                                                   (succ
                                                                                                                      (add
                                                                                                                         n_n
                                                                                                                         n_n_1))))
                                                                                                           (eq.rec
                                                                                                              (eq.refl
                                                                                                                 (succ
                                                                                                                      (add
                                                                                                                         (succ
                                                                                                                            n_n)
                                                                                                                         n_n_1) =
                                                                                                                    succ
                                                                                                                      (succ
                                                                                                                         (add
                                                                                                                            n_n
                                                                                                                            n_n_1))))
                                                                                                              (propext
                                                                                                                 {mp := λ
                                                                                                                        (h :
                                                                                                                          succ
                                                                                                                              (add
                                                                                                                                 (succ
                                                                                                                                    n_n)
                                                                                                                                 n_n_1) =
                                                                                                                            succ
                                                                                                                              (succ
                                                                                                                                 (add
                                                                                                                                    n_n
                                                                                                                                    n_n_1))),
                                                                                                                          eq.rec
                                                                                                                            (λ
                                                                                                                             (h11 :
                                                                                                                               succ
                                                                                                                                   … =
                                                                                                                                 succ
                                                                                                                                   …)
                                                                                                                             (a :
                                                                                                                               … =
                                                                                                                                 … →
                                                                                                                               … =
                                                                                                                                 …),
                                                                                                                               a
                                                                                                                                 (eq.refl
                                                                                                                                    …))
                                                                                                                            h
                                                                                                                            h
                                                                                                                            (λ
                                                                                                                             (n_eq :
                                                                                                                               add
                                                                                                                                   (succ
                                                                                                                                      n_n)
                                                                                                                                   n_n_1 =
                                                                                                                                 succ
                                                                                                                                   (add
                                                                                                                                      n_n
                                                                                                                                      n_n_1)),
                                                                                                                               n_eq),
                                                                                                                  mpr := λ
                                                                                                                         (a :
                                                                                                                           add
                                                                                                                               (succ
                                                                                                                                  n_n)
                                                                                                                               n_n_1 =
                                                                                                                             succ
                                                                                                                               (add
                                                                                                                                  n_n
                                                                                                                                  n_n_1)),
                                                                                                                           eq.rec
                                                                                                                             (eq.refl
                                                                                                                                (succ
                                                                                                                                   (add
                                                                                                                                      (succ
                                                                                                                                         n_n)
                                                                                                                                      n_n_1)))
                                                                                                                             a}))))
                                                                                                   n_1)
                                                                                                (eq.rec
                                                                                                   (eq.refl
                                                                                                      (succ
                                                                                                           (add
                                                                                                              (succ n_n)
                                                                                                              n_1) =
                                                                                                         succ
                                                                                                           (succ
                                                                                                              (add n_n
                                                                                                                 n_1))))
                                                                                                   (eq.rec
                                                                                                      (eq.refl
                                                                                                         (succ
                                                                                                              (add
                                                                                                                 (succ
                                                                                                                    n_n)
                                                                                                                 n_1) =
                                                                                                            succ
                                                                                                              (succ
                                                                                                                 (add
                                                                                                                    n_n
                                                                                                                    n_1))))
                                                                                                      (propext
                                                                                                         {mp := λ
                                                                                                                (h :
                                                                                                                  succ
                                                                                                                      (add
                                                                                                                         (succ
                                                                                                                            n_n)
                                                                                                                         n_1) =
                                                                                                                    succ
                                                                                                                      (succ
                                                                                                                         (add
                                                                                                                            n_n
                                                                                                                            n_1))),
                                                                                                                  eq.rec
                                                                                                                    (λ
                                                                                                                     (h11 :
                                                                                                                       succ
                                                                                                                           (add
                                                                                                                              (succ
                                                                                                                                 n_n)
                                                                                                                              n_1) =
                                                                                                                         succ
                                                                                                                           (add
                                                                                                                              (succ
                                                                                                                                 n_n)
                                                                                                                              n_1))
                                                                                                                     (a :
                                                                                                                       add
                                                                                                                           (succ
                                                                                                                              n_n)
                                                                                                                           n_1 =
                                                                                                                         add
                                                                                                                           (succ
                                                                                                                              n_n)
                                                                                                                           n_1 →
                                                                                                                       add
                                                                                                                           (succ
                                                                                                                              n_n)
                                                                                                                           n_1 =
                                                                                                                         succ
                                                                                                                           (add
                                                                                                                              n_n
                                                                                                                              n_1)),
                                                                                                                       a
                                                                                                                         (eq.refl
                                                                                                                            (add
                                                                                                                               (succ
                                                                                                                                  n_n)
                                                                                                                               n_1)))
                                                                                                                    h
                                                                                                                    h
                                                                                                                    (λ
                                                                                                                     (n_eq :
                                                                                                                       add
                                                                                                                           (succ
                                                                                                                              n_n)
                                                                                                                           n_1 =
                                                                                                                         succ
                                                                                                                           (add
                                                                                                                              n_n
                                                                                                                              n_1)),
                                                                                                                       n_eq),
                                                                                                          mpr := λ
                                                                                                                 (a :
                                                                                                                   add
                                                                                                                       (succ
                                                                                                                          n_n)
                                                                                                                       n_1 =
                                                                                                                     succ
                                                                                                                       (add
                                                                                                                          n_n
                                                                                                                          n_1)),
                                                                                                                   eq.rec
                                                                                                                     (eq.refl
                                                                                                                        (succ
                                                                                                                           (add
                                                                                                                              (succ
                                                                                                                                 n_n)
                                                                                                                              n_1)))
                                                                                                                     a})))))
                                                                                          (propext
                                                                                             {mp := λ
                                                                                                    (h :
                                                                                                      succ
                                                                                                          (add
                                                                                                             (succ n_1)
                                                                                                             n_n) =
                                                                                                        succ
                                                                                                          (succ
                                                                                                             (add n_n
                                                                                                                n_1))),
                                                                                                      eq.rec
                                                                                                        (λ
                                                                                                         (h11 :
                                                                                                           succ
                                                                                                               (add
                                                                                                                  (succ
                                                                                                                     n_1)
                                                                                                                  n_n) =
                                                                                                             succ
                                                                                                               (add
                                                                                                                  (succ
                                                                                                                     n_1)
                                                                                                                  n_n))
                                                                                                         (a :
                                                                                                           add
                                                                                                               (succ
                                                                                                                  n_1)
                                                                                                               n_n =
                                                                                                             add
                                                                                                               (succ
                                                                                                                  n_1)
                                                                                                               n_n →
                                                                                                           add
                                                                                                               (succ
                                                                                                                  n_1)
                                                                                                               n_n =
                                                                                                             succ
                                                                                                               (add n_n
                                                                                                                  n_1)),
                                                                                                           a
                                                                                                             (eq.refl
                                                                                                                (add
                                                                                                                   (succ
                                                                                                                      n_1)
                                                                                                                   n_n)))
                                                                                                        h
                                                                                                        h
                                                                                                        (λ
                                                                                                         (n_eq :
                                                                                                           add
                                                                                                               (succ
                                                                                                                  n_1)
                                                                                                               n_n =
                                                                                                             succ
                                                                                                               (add n_n
                                                                                                                  n_1)),
                                                                                                           n_eq),
                                                                                              mpr := λ
                                                                                                     (a :
                                                                                                       add (succ n_1)
                                                                                                           n_n =
                                                                                                         succ
                                                                                                           (add n_n
                                                                                                              n_1)),
                                                                                                       eq.rec
                                                                                                         (eq.refl
                                                                                                            (succ
                                                                                                               (add
                                                                                                                  (succ
                                                                                                                     n_1)
                                                                                                                  n_n)))
                                                                                                         a}))))
                                                                               (mul m n))))).mp
                                                                     ha)})))
                                           m
                                           hmn0)))
                                w
                                (eq.rec (eq.refl zero)
                                   (mynat.rec
                                      (eq.rec
                                         (λ (a : zero = mul m w),
                                            eq.rec true.intro
                                              (eq.rec (eq.refl (zero = mul m w))
                                                 (propext
                                                    {mp := λ (hl : zero = mul m w), true.intro,
                                                     mpr := λ (hr : true), a})))
                                         (eq.rec (eq.refl (zero = add zero (mul m w) → zero = mul m w))
                                            (propext
                                               {mp := λ (hab : zero = add zero (mul m w) → zero = mul m w)
                                                      (hc : zero = mul m w),
                                                        hab
                                                          ((eq.rec
                                                              {mp := λ (h : zero = add zero (mul m w)), h,
                                                               mpr := λ (h : zero = add zero (mul m w)), h}
                                                              (eq.rec (eq.refl (zero = add zero (mul m w)))
                                                                 (eq.rec (eq.refl (add zero (mul m w)))
                                                                    (mynat.rec
                                                                       (eq.rec true.intro
                                                                          (eq.rec (eq.refl (zero = zero))
                                                                             (eq.rec (eq.refl (zero = zero))
                                                                                (propext
                                                                                   {mp := λ (hl : zero = zero),
                                                                                            true.intro,
                                                                                    mpr := λ (hr : true),
                                                                                             eq.refl zero}))))
                                                                       (λ (n_n : mynat) (n_ih : add zero n_n = n_n),
                                                                          eq.rec n_ih
                                                                            (eq.rec
                                                                               (eq.refl
                                                                                  (succ (add zero n_n) = succ n_n))
                                                                               (eq.rec
                                                                                  (eq.refl
                                                                                     (succ (add zero n_n) = succ n_n))
                                                                                  (propext
                                                                                     {mp := λ
                                                                                            (h :
                                                                                              succ (add zero n_n) =
                                                                                                succ n_n),
                                                                                              eq.rec
                                                                                                (λ
                                                                                                 (h11 :
                                                                                                   succ (add zero n_n) =
                                                                                                     succ
                                                                                                       (add zero n_n))
                                                                                                 (a :
                                                                                                   add zero n_n =
                                                                                                     add zero n_n →
                                                                                                   add zero n_n = n_n),
                                                                                                   a
                                                                                                     (eq.refl
                                                                                                        (add zero n_n)))
                                                                                                h
                                                                                                h
                                                                                                (λ
                                                                                                 (n_eq :
                                                                                                   add zero n_n = n_n),
                                                                                                   n_eq),
                                                                                      mpr := λ
                                                                                             (a : add zero n_n = n_n),
                                                                                               eq.rec
                                                                                                 (eq.refl
                                                                                                    (succ
                                                                                                       (add zero n_n)))
                                                                                                 a}))))
                                                                       (mul m w))))).mpr
                                                             hc),
                                                mpr := λ (hcd : zero = mul m w → zero = mul m w)
                                                       (ha : zero = add zero (mul m w)),
                                                         hcd
                                                           ((eq.rec
                                                               {mp := λ (h : zero = add zero (mul m w)), h,
                                                                mpr := λ (h : zero = add zero (mul m w)), h}
                                                               (eq.rec (eq.refl (zero = add zero (mul m w)))
                                                                  (eq.rec (eq.refl (add zero (mul m w)))
                                                                     (mynat.rec
                                                                        (eq.rec true.intro
                                                                           (eq.rec (eq.refl (zero = zero))
                                                                              (eq.rec (eq.refl (zero = zero))
                                                                                 (propext
                                                                                    {mp := λ (hl : zero = zero),
                                                                                             true.intro,
                                                                                     mpr := λ (hr : true),
                                                                                              eq.refl zero}))))
                                                                        (λ (n_n : mynat) (n_ih : add zero n_n = n_n),
                                                                           eq.rec n_ih
                                                                             (eq.rec
                                                                                (eq.refl
                                                                                   (succ (add zero n_n) = succ n_n))
                                                                                (eq.rec
                                                                                   (eq.refl
                                                                                      (succ (add zero n_n) = succ n_n))
                                                                                   (propext
                                                                                      {mp := λ
                                                                                             (h :
                                                                                               succ (add zero n_n) =
                                                                                                 succ n_n),
                                                                                               eq.rec
                                                                                                 (λ
                                                                                                  (h11 :
                                                                                                    succ
                                                                                                        (add zero n_n) =
                                                                                                      succ
                                                                                                        (add zero n_n))
                                                                                                  (a :
                                                                                                    add zero n_n =
                                                                                                      add zero n_n →
                                                                                                    add zero n_n = n_n),
                                                                                                    a
                                                                                                      (eq.refl
                                                                                                         (add zero
                                                                                                            n_n)))
                                                                                                 h
                                                                                                 h
                                                                                                 (λ
                                                                                                  (n_eq :
                                                                                                    add zero n_n = n_n),
                                                                                                    n_eq),
                                                                                       mpr := λ
                                                                                              (a : add zero n_n = n_n),
                                                                                                eq.rec
                                                                                                  (eq.refl
                                                                                                     (succ
                                                                                                        (add zero n_n)))
                                                                                                  a}))))
                                                                        (mul m w))))).mp
                                                              ha)})))
                                      (λ (m_n : mynat) (m_ih : m_n = add m_n (mul m w) → zero = mul m w),
                                         eq.rec
                                           (eq.rec
                                              (eq.rec m_ih
                                                 (eq.rec (eq.refl (m_n = add (mul m w) m_n → zero = mul m w))
                                                    (eq.rec (eq.refl (m_n = add (mul m w) m_n → zero = mul m w))
                                                       (mynat.rec
                                                          (eq.rec true.intro
                                                             (eq.rec (eq.refl (mul m w = add zero (mul m w)))
                                                                (eq.rec
                                                                   (eq.rec (eq.refl (mul m w = add zero (mul m w)))
                                                                      (eq.rec (eq.refl (add zero (mul m w)))
                                                                         (mynat.rec (eq.refl zero)
                                                                            (λ (m_n : mynat)
                                                                             (m_ih : add zero m_n = m_n),
                                                                               eq.rec m_ih
                                                                                 (eq.rec
                                                                                    (eq.refl
                                                                                       (succ (add zero m_n) = succ m_n))
                                                                                    (eq.rec
                                                                                       (eq.refl
                                                                                          (succ (add zero m_n) =
                                                                                             succ m_n))
                                                                                       (propext
                                                                                          {mp := λ
                                                                                                 (h :
                                                                                                   succ (add zero m_n) =
                                                                                                     succ m_n),
                                                                                                   eq.rec
                                                                                                     (λ
                                                                                                      (h11 :
                                                                                                        succ
                                                                                                            (add zero
                                                                                                               m_n) =
                                                                                                          succ
                                                                                                            (add zero
                                                                                                               m_n))
                                                                                                      (a :
                                                                                                        add zero m_n =
                                                                                                          add zero
                                                                                                            m_n →
                                                                                                        add zero m_n =
                                                                                                          m_n),
                                                                                                        a
                                                                                                          (eq.refl
                                                                                                             (add zero
                                                                                                                m_n)))
                                                                                                     h
                                                                                                     h
                                                                                                     (λ
                                                                                                      (n_eq :
                                                                                                        add zero m_n =
                                                                                                          m_n), n_eq),
                                                                                           mpr := λ
                                                                                                  (a :
                                                                                                    add zero m_n = m_n),
                                                                                                    eq.rec
                                                                                                      (eq.refl
                                                                                                         (succ
                                                                                                            (add zero
                                                                                                               m_n)))
                                                                                                      a}))))
                                                                            (mul m w))))
                                                                   (propext
                                                                      {mp := λ (hl : mul m w = mul m w), true.intro,
                                                                       mpr := λ (hr : true), eq.refl (mul m w)}))))
                                                          (λ (n_n : mynat)
                                                           (n_ih : add (mul m w) n_n = add n_n (mul m w)),
                                                             eq.rec n_ih
                                                               (eq.rec
                                                                  (eq.refl
                                                                     (succ (add (mul m w) n_n) =
                                                                        add (succ n_n) (mul m w)))
                                                                  (eq.rec
                                                                     (eq.rec
                                                                        (eq.refl
                                                                           (succ (add (mul m w) n_n) =
                                                                              add (succ n_n) (mul m w)))
                                                                        (mynat.rec (eq.refl (succ n_n))
                                                                           (λ (n_n_1 : mynat)
                                                                            (n_ih :
                                                                              add (succ n_n) n_n_1 =
                                                                                succ (add n_n n_n_1)),
                                                                              eq.rec n_ih
                                                                                (eq.rec
                                                                                   (eq.refl
                                                                                      (succ (add (succ n_n) n_n_1) =
                                                                                         succ (succ (add n_n n_n_1))))
                                                                                   (eq.rec
                                                                                      (eq.refl
                                                                                         (succ (add (succ n_n) n_n_1) =
                                                                                            succ
                                                                                              (succ (add n_n n_n_1))))
                                                                                      (propext
                                                                                         {mp := λ
                                                                                                (h :
                                                                                                  succ
                                                                                                      (add (succ n_n)
                                                                                                         n_n_1) =
                                                                                                    succ
                                                                                                      (succ
                                                                                                         (add n_n
                                                                                                            n_n_1))),
                                                                                                  eq.rec
                                                                                                    (λ
                                                                                                     (h11 :
                                                                                                       succ
                                                                                                           (add
                                                                                                              (succ n_n)
                                                                                                              n_n_1) =
                                                                                                         succ
                                                                                                           (add
                                                                                                              (succ n_n)
                                                                                                              n_n_1))
                                                                                                     (a :
                                                                                                       add (succ n_n)
                                                                                                           n_n_1 =
                                                                                                         add (succ n_n)
                                                                                                           n_n_1 →
                                                                                                       add (succ n_n)
                                                                                                           n_n_1 =
                                                                                                         succ
                                                                                                           (add n_n
                                                                                                              n_n_1)),
                                                                                                       a
                                                                                                         (eq.refl
                                                                                                            (add
                                                                                                               (succ
                                                                                                                  n_n)
                                                                                                               n_n_1)))
                                                                                                    h
                                                                                                    h
                                                                                                    (λ
                                                                                                     (n_eq :
                                                                                                       add (succ n_n)
                                                                                                           n_n_1 =
                                                                                                         succ
                                                                                                           (add n_n
                                                                                                              n_n_1)),
                                                                                                       n_eq),
                                                                                          mpr := λ
                                                                                                 (a :
                                                                                                   add (succ n_n)
                                                                                                       n_n_1 =
                                                                                                     succ
                                                                                                       (add n_n n_n_1)),
                                                                                                   eq.rec
                                                                                                     (eq.refl
                                                                                                        (succ
                                                                                                           (add
                                                                                                              (succ n_n)
                                                                                                              n_n_1)))
                                                                                                     a}))))
                                                                           (mul m w)))
                                                                     (propext
                                                                        {mp := λ
                                                                               (h :
                                                                                 succ (add (mul m w) n_n) =
                                                                                   succ (add n_n (mul m w))),
                                                                                 eq.rec
                                                                                   (λ
                                                                                    (h11 :
                                                                                      succ (add (mul m w) n_n) =
                                                                                        succ (add (mul m w) n_n))
                                                                                    (a :
                                                                                      add (mul m w) n_n =
                                                                                        add (mul m w) n_n →
                                                                                      add (mul m w) n_n =
                                                                                        add n_n (mul m w)),
                                                                                      a (eq.refl (add (mul m w) n_n)))
                                                                                   h
                                                                                   h
                                                                                   (λ
                                                                                    (n_eq :
                                                                                      add (mul m w) n_n =
                                                                                        add n_n (mul m w)), n_eq),
                                                                         mpr := λ
                                                                                (a :
                                                                                  add (mul m w) n_n =
                                                                                    add n_n (mul m w)),
                                                                                  eq.rec
                                                                                    (eq.refl (succ (add (mul m w) n_n)))
                                                                                    a}))))
                                                          m_n))))
                                              (eq.rec (eq.refl (add zero m_n = add (mul m w) m_n → zero = mul m w))
                                                 (eq.rec (eq.refl (add zero m_n = add (mul m w) m_n → zero = mul m w))
                                                    (mynat.rec
                                                       (eq.rec true.intro
                                                          (eq.rec (eq.refl (zero = zero))
                                                             (eq.rec (eq.refl (zero = zero))
                                                                (propext
                                                                   {mp := λ (hl : zero = zero), true.intro,
                                                                    mpr := λ (hr : true), eq.refl zero}))))
                                                       (λ (n_n : mynat) (n_ih : add zero n_n = n_n),
                                                          eq.rec n_ih
                                                            (eq.rec (eq.refl (succ (add zero n_n) = succ n_n))
                                                               (eq.rec (eq.refl (succ (add zero n_n) = succ n_n))
                                                                  (propext
                                                                     {mp := λ (h : succ (add zero n_n) = succ n_n),
                                                                              eq.rec
                                                                                (λ
                                                                                 (h11 :
                                                                                   succ (add zero n_n) =
                                                                                     succ (add zero n_n))
                                                                                 (a :
                                                                                   add zero n_n = add zero n_n →
                                                                                   add zero n_n = n_n),
                                                                                   a (eq.refl (add zero n_n)))
                                                                                h
                                                                                h
                                                                                (λ (n_eq : add zero n_n = n_n), n_eq),
                                                                      mpr := λ (a : add zero n_n = n_n),
                                                                               eq.rec (eq.refl (succ (add zero n_n)))
                                                                                 a}))))
                                                       m_n))))
                                           (eq.rec (eq.refl (succ m_n = add (succ m_n) (mul m w) → zero = mul m w))
                                              (propext
                                                 {mp := λ
                                                        (hab : succ m_n = add (succ m_n) (mul m w) → zero = mul m w)
                                                        (hc : add zero m_n = add (mul m w) m_n),
                                                          hab
                                                            ((eq.rec
                                                                {mp := λ (h : succ m_n = add (succ m_n) (mul m w)), h,
                                                                 mpr := λ (h : succ m_n = add (succ m_n) (mul m w)), h}
                                                                (eq.rec
                                                                   (eq.rec
                                                                      (eq.rec
                                                                         (eq.refl (succ m_n = add (succ m_n) (mul m w)))
                                                                         (mynat.rec
                                                                            (eq.rec true.intro
                                                                               (eq.rec
                                                                                  (eq.refl
                                                                                     (succ m_n = succ (add zero m_n)))
                                                                                  (eq.rec
                                                                                     (eq.rec
                                                                                        (eq.refl
                                                                                           (succ m_n =
                                                                                              succ (add zero m_n)))
                                                                                        (eq.rec
                                                                                           (eq.refl
                                                                                              (succ (add zero m_n)))
                                                                                           (eq.rec
                                                                                              (mynat.rec (eq.refl zero)
                                                                                                 (λ (m_n : mynat)
                                                                                                  (m_ih :
                                                                                                    add zero m_n = m_n),
                                                                                                    eq.rec m_ih
                                                                                                      (eq.rec
                                                                                                         (eq.refl
                                                                                                            (succ
                                                                                                                 (add
                                                                                                                    zero
                                                                                                                    m_n) =
                                                                                                               succ
                                                                                                                 m_n))
                                                                                                         (eq.rec
                                                                                                            (eq.refl
                                                                                                               (succ
                                                                                                                    (add
                                                                                                                       zero
                                                                                                                       m_n) =
                                                                                                                  succ
                                                                                                                    m_n))
                                                                                                            (propext
                                                                                                               {mp := λ
                                                                                                                      (h :
                                                                                                                        succ
                                                                                                                            (add
                                                                                                                               zero
                                                                                                                               m_n) =
                                                                                                                          succ
                                                                                                                            m_n),
                                                                                                                        eq.rec
                                                                                                                          (λ
                                                                                                                           (h11 :
                                                                                                                             succ
                                                                                                                                 … =
                                                                                                                               succ
                                                                                                                                 …)
                                                                                                                           (a :
                                                                                                                             … =
                                                                                                                               … →
                                                                                                                             … =
                                                                                                                               m_n),
                                                                                                                             a
                                                                                                                               (eq.refl
                                                                                                                                  …))
                                                                                                                          h
                                                                                                                          h
                                                                                                                          (λ
                                                                                                                           (n_eq :
                                                                                                                             add
                                                                                                                                 zero
                                                                                                                                 m_n =
                                                                                                                               m_n),
                                                                                                                             n_eq),
                                                                                                                mpr := …}))))
                                                                                                 m_n)
                                                                                              …)))
                                                                                     …)))
                                                                            …
                                                                            …))
                                                                      …)
                                                                   …)).mpr
                                                               hc),
                                                  mpr := …})))
                                      …
                                      …))))))
                    …)))
         h
         h)
    …
    …
    …
