λ (statement : mynat → Prop) (base_case : statement zero)
(inductive_step :
  ∀ (n : mynat), (∀ (m : mynat), (∃ (k : mynat), n = add m k) → statement m) → statement (succ n))
(k : mynat),
  mynat.rec
    (λ (M : mynat) (hMl0 : ∃ (k : mynat), zero = add M k),
       eq.rec base_case
         (eq.rec (eq.refl (statement M))
            (eq.rec (eq.refl (statement M))
               (Exists.rec
                  (λ (w : mynat) (h : zero = add M w) («_» : ∃ (k : mynat), zero = add M k),
                     mynat.rec
                       (eq.rec true.intro
                          (eq.rec (eq.refl (add zero w = zero → zero = zero))
                             (eq.rec
                                (propext
                                   {mp := λ (hab : add zero w = zero → zero = zero) (hc : w = zero),
                                            (eq.rec {mp := λ (h : zero = zero), h, mpr := λ (h : zero = zero), h}
                                               (eq.rec (eq.refl (zero = zero))
                                                  (propext
                                                     {mp := λ (hl : zero = zero), true.intro,
                                                      mpr := λ (hr : true), eq.refl zero}))).mp
                                              (hab
                                                 ((eq.rec
                                                     {mp := λ (h : add zero w = zero), h,
                                                      mpr := λ (h : add zero w = zero), h}
                                                     (eq.rec (eq.refl (add zero w = zero))
                                                        (eq.rec (eq.refl (eq (add zero w)))
                                                           (eq.rec (eq.refl (add zero w))
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
                                                                         (eq.rec
                                                                            (eq.refl (succ (add zero n_n) = succ n_n))
                                                                            (propext
                                                                               {mp := λ
                                                                                      (h :
                                                                                        succ (add zero n_n) = succ n_n),
                                                                                        eq.rec
                                                                                          (λ
                                                                                           (h11 :
                                                                                             succ (add zero n_n) =
                                                                                               succ (add zero n_n))
                                                                                           (a :
                                                                                             add zero n_n =
                                                                                               add zero n_n →
                                                                                             add zero n_n = n_n),
                                                                                             a (eq.refl (add zero n_n)))
                                                                                          h
                                                                                          h
                                                                                          (λ
                                                                                           (n_eq : add zero n_n = n_n),
                                                                                             n_eq),
                                                                                mpr := λ (a : add zero n_n = n_n),
                                                                                         eq.rec
                                                                                           (eq.refl
                                                                                              (succ (add zero n_n)))
                                                                                           a}))))
                                                                 w))))).mpr
                                                    hc)),
                                    mpr := λ (hcd : w = zero → true) (ha : add zero w = zero),
                                             (eq.rec {mp := λ (h : zero = zero), h, mpr := λ (h : zero = zero), h}
                                                (eq.rec (eq.refl (zero = zero))
                                                   (propext
                                                      {mp := λ (hl : zero = zero), true.intro,
                                                       mpr := λ (hr : true), eq.refl zero}))).mpr
                                               (hcd
                                                  ((eq.rec
                                                      {mp := λ (h : add zero w = zero), h,
                                                       mpr := λ (h : add zero w = zero), h}
                                                      (eq.rec (eq.refl (add zero w = zero))
                                                         (eq.rec (eq.refl (eq (add zero w)))
                                                            (eq.rec (eq.refl (add zero w))
                                                               (mynat.rec
                                                                  (eq.rec true.intro
                                                                     (eq.rec (eq.refl (zero = zero))
                                                                        (eq.rec (eq.refl (zero = zero))
                                                                           (propext
                                                                              {mp := λ (hl : zero = zero), true.intro,
                                                                               mpr := λ (hr : true), eq.refl zero}))))
                                                                  (λ (n_n : mynat) (n_ih : add zero n_n = n_n),
                                                                     eq.rec n_ih
                                                                       (eq.rec
                                                                          (eq.refl (succ (add zero n_n) = succ n_n))
                                                                          (eq.rec
                                                                             (eq.refl (succ (add zero n_n) = succ n_n))
                                                                             (propext
                                                                                {mp := λ
                                                                                       (h :
                                                                                         succ (add zero n_n) =
                                                                                           succ n_n),
                                                                                         eq.rec
                                                                                           (λ
                                                                                            (h11 :
                                                                                              succ (add zero n_n) =
                                                                                                succ (add zero n_n))
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
                                                                                            (n_eq : add zero n_n = n_n),
                                                                                              n_eq),
                                                                                 mpr := λ (a : add zero n_n = n_n),
                                                                                          eq.rec
                                                                                            (eq.refl
                                                                                               (succ (add zero n_n)))
                                                                                            a}))))
                                                                  w))))).mp
                                                     ha))})
                                (propext
                                   {mp := λ (h : w = zero → true), true.intro,
                                    mpr := λ (ha : true) (h : w = zero), true.intro}))))
                       (λ (n : mynat) (ih : add n w = zero → n = zero),
                          eq.rec
                            (λ (hsmnz : succ (add w n) = zero),
                               false.rec (succ n = zero)
                                 (eq.rec
                                    (λ («_» : succ (add w n) = succ (add w n)) (a : zero = succ (add w n)),
                                       eq.rec
                                         (λ (h11 : zero = zero) (a : hsmnz == eq.refl (succ (add w n)) → false), a)
                                         a
                                         a)
                                    hsmnz
                                    hsmnz
                                    (eq.refl zero)
                                    (heq.refl hsmnz)))
                            (eq.rec (eq.refl (add (succ n) w = zero → succ n = zero))
                               (propext
                                  {mp := λ (hab : add (succ n) w = zero → succ n = zero)
                                         (hc : succ (add w n) = zero),
                                           hab
                                             ((eq.rec
                                                 {mp := λ (h : add (succ n) w = zero), h,
                                                  mpr := λ (h : add (succ n) w = zero), h}
                                                 (eq.rec (eq.refl (add (succ n) w = zero))
                                                    (eq.rec (eq.refl (eq (add (succ n) w)))
                                                       (mynat.rec
                                                          (eq.rec true.intro
                                                             (eq.rec (eq.refl (succ n = succ (add zero n)))
                                                                (eq.rec
                                                                   (eq.rec (eq.refl (succ n = succ (add zero n)))
                                                                      (eq.rec (eq.refl (succ (add zero n)))
                                                                         (eq.rec
                                                                            (mynat.rec (eq.refl zero)
                                                                               (λ (m_n : mynat)
                                                                                (m_ih : add zero m_n = m_n),
                                                                                  eq.rec m_ih
                                                                                    (eq.rec
                                                                                       (eq.refl
                                                                                          (succ (add zero m_n) =
                                                                                             succ m_n))
                                                                                       (eq.rec
                                                                                          (eq.refl
                                                                                             (succ (add zero m_n) =
                                                                                                succ m_n))
                                                                                          (propext
                                                                                             {mp := λ
                                                                                                    (h :
                                                                                                      succ
                                                                                                          (add zero
                                                                                                             m_n) =
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
                                                                                                           add zero
                                                                                                               m_n =
                                                                                                             add zero
                                                                                                               m_n →
                                                                                                           add zero
                                                                                                               m_n =
                                                                                                             m_n),
                                                                                                           a
                                                                                                             (eq.refl
                                                                                                                (add
                                                                                                                   zero
                                                                                                                   m_n)))
                                                                                                        h
                                                                                                        h
                                                                                                        (λ
                                                                                                         (n_eq :
                                                                                                           add zero
                                                                                                               m_n =
                                                                                                             m_n),
                                                                                                           n_eq),
                                                                                              mpr := λ
                                                                                                     (a :
                                                                                                       add zero m_n =
                                                                                                         m_n),
                                                                                                       eq.rec
                                                                                                         (eq.refl
                                                                                                            (succ
                                                                                                               (add zero
                                                                                                                  m_n)))
                                                                                                         a}))))
                                                                               n)
                                                                            (eq.rec
                                                                               (eq.refl (succ (add zero n) = succ n))
                                                                               (eq.rec
                                                                                  (eq.refl (succ (add zero n) = succ n))
                                                                                  (propext
                                                                                     {mp := λ
                                                                                            (h :
                                                                                              succ (add zero n) =
                                                                                                succ n),
                                                                                              eq.rec
                                                                                                (λ
                                                                                                 (h11 :
                                                                                                   succ (add zero n) =
                                                                                                     succ (add zero n))
                                                                                                 (a :
                                                                                                   add zero n =
                                                                                                     add zero n →
                                                                                                   add zero n = n),
                                                                                                   a
                                                                                                     (eq.refl
                                                                                                        (add zero n)))
                                                                                                h
                                                                                                h
                                                                                                (λ
                                                                                                 (n_eq :
                                                                                                   add zero n = n),
                                                                                                   n_eq),
                                                                                      mpr := λ (a : add zero n = n),
                                                                                               eq.rec
                                                                                                 (eq.refl
                                                                                                    (succ (add zero n)))
                                                                                                 a}))))))
                                                                   (propext
                                                                      {mp := λ (hl : succ n = succ n), true.intro,
                                                                       mpr := λ (hr : true), eq.refl (succ n)}))))
                                                          (λ (n_n : mynat)
                                                           (n_ih : add (succ n) n_n = succ (add n_n n)),
                                                             eq.rec n_ih
                                                               (eq.rec
                                                                  (eq.refl
                                                                     (succ (add (succ n) n_n) =
                                                                        succ (add (succ n_n) n)))
                                                                  (eq.rec
                                                                     (eq.rec
                                                                        (eq.refl
                                                                           (succ (add (succ n) n_n) =
                                                                              succ (add (succ n_n) n)))
                                                                        (eq.rec
                                                                           (mynat.rec (eq.refl (succ n_n))
                                                                              (λ (n_n_1 : mynat)
                                                                               (n_ih :
                                                                                 add (succ n_n) n_n_1 =
                                                                                   succ (add n_n n_n_1)),
                                                                                 eq.rec n_ih
                                                                                   (eq.rec
                                                                                      (eq.refl
                                                                                         (succ (add (succ n_n) n_n_1) =
                                                                                            succ
                                                                                              (succ (add n_n n_n_1))))
                                                                                      (eq.rec
                                                                                         (eq.refl
                                                                                            (succ
                                                                                                 (add (succ n_n)
                                                                                                    n_n_1) =
                                                                                               succ
                                                                                                 (succ
                                                                                                    (add n_n n_n_1))))
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
                                                                                                                 (succ
                                                                                                                    n_n)
                                                                                                                 n_n_1) =
                                                                                                            succ
                                                                                                              (add
                                                                                                                 (succ
                                                                                                                    n_n)
                                                                                                                 n_n_1))
                                                                                                        (a :
                                                                                                          add (succ n_n)
                                                                                                              n_n_1 =
                                                                                                            add
                                                                                                              (succ n_n)
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
                                                                                                          (add n_n
                                                                                                             n_n_1)),
                                                                                                      eq.rec
                                                                                                        (eq.refl
                                                                                                           (succ
                                                                                                              (add
                                                                                                                 (succ
                                                                                                                    n_n)
                                                                                                                 n_n_1)))
                                                                                                        a}))))
                                                                              n)
                                                                           (eq.rec
                                                                              (eq.refl
                                                                                 (succ (add (succ n_n) n) =
                                                                                    succ (succ (add n_n n))))
                                                                              (eq.rec
                                                                                 (eq.refl
                                                                                    (succ (add (succ n_n) n) =
                                                                                       succ (succ (add n_n n))))
                                                                                 (propext
                                                                                    {mp := λ
                                                                                           (h :
                                                                                             succ (add (succ n_n) n) =
                                                                                               succ (succ (add n_n n))),
                                                                                             eq.rec
                                                                                               (λ
                                                                                                (h11 :
                                                                                                  succ
                                                                                                      (add (succ n_n)
                                                                                                         n) =
                                                                                                    succ
                                                                                                      (add (succ n_n)
                                                                                                         n))
                                                                                                (a :
                                                                                                  add (succ n_n) n =
                                                                                                    add (succ n_n) n →
                                                                                                  add (succ n_n) n =
                                                                                                    succ (add n_n n)),
                                                                                                  a
                                                                                                    (eq.refl
                                                                                                       (add (succ n_n)
                                                                                                          n)))
                                                                                               h
                                                                                               h
                                                                                               (λ
                                                                                                (n_eq :
                                                                                                  add (succ n_n) n =
                                                                                                    succ (add n_n n)),
                                                                                                  n_eq),
                                                                                     mpr := λ
                                                                                            (a :
                                                                                              add (succ n_n) n =
                                                                                                succ (add n_n n)),
                                                                                              eq.rec
                                                                                                (eq.refl
                                                                                                   (succ
                                                                                                      (add (succ n_n)
                                                                                                         n)))
                                                                                                a})))))
                                                                     (propext
                                                                        {mp := λ
                                                                               (h :
                                                                                 succ (add (succ n) n_n) =
                                                                                   succ (succ (add n_n n))),
                                                                                 eq.rec
                                                                                   (λ
                                                                                    (h11 :
                                                                                      succ (add (succ n) n_n) =
                                                                                        succ (add (succ n) n_n))
                                                                                    (a :
                                                                                      add (succ n) n_n =
                                                                                        add (succ n) n_n →
                                                                                      add (succ n) n_n =
                                                                                        succ (add n_n n)),
                                                                                      a (eq.refl (add (succ n) n_n)))
                                                                                   h
                                                                                   h
                                                                                   (λ
                                                                                    (n_eq :
                                                                                      add (succ n) n_n =
                                                                                        succ (add n_n n)), n_eq),
                                                                         mpr := λ
                                                                                (a :
                                                                                  add (succ n) n_n = succ (add n_n n)),
                                                                                  eq.rec
                                                                                    (eq.refl (succ (add (succ n) n_n)))
                                                                                    a}))))
                                                          w)))).mpr
                                                hc),
                                   mpr := λ (hcd : succ (add w n) = zero → succ n = zero)
                                          (ha : add (succ n) w = zero),
                                            hcd
                                              ((eq.rec
                                                  {mp := λ (h : add (succ n) w = zero), h,
                                                   mpr := λ (h : add (succ n) w = zero), h}
                                                  (eq.rec (eq.refl (add (succ n) w = zero))
                                                     (eq.rec (eq.refl (eq (add (succ n) w)))
                                                        (mynat.rec
                                                           (eq.rec true.intro
                                                              (eq.rec (eq.refl (succ n = succ (add zero n)))
                                                                 (eq.rec
                                                                    (eq.rec (eq.refl (succ n = succ (add zero n)))
                                                                       (eq.rec (eq.refl (succ (add zero n)))
                                                                          (eq.rec
                                                                             (mynat.rec (eq.refl zero)
                                                                                (λ (m_n : mynat)
                                                                                 (m_ih : add zero m_n = m_n),
                                                                                   eq.rec m_ih
                                                                                     (eq.rec
                                                                                        (eq.refl
                                                                                           (succ (add zero m_n) =
                                                                                              succ m_n))
                                                                                        (eq.rec
                                                                                           (eq.refl
                                                                                              (succ (add zero m_n) =
                                                                                                 succ m_n))
                                                                                           (propext
                                                                                              {mp := λ
                                                                                                     (h :
                                                                                                       succ
                                                                                                           (add zero
                                                                                                              m_n) =
                                                                                                         succ m_n),
                                                                                                       eq.rec
                                                                                                         (λ
                                                                                                          (h11 :
                                                                                                            succ
                                                                                                                (add
                                                                                                                   zero
                                                                                                                   m_n) =
                                                                                                              succ
                                                                                                                (add
                                                                                                                   zero
                                                                                                                   m_n))
                                                                                                          (a :
                                                                                                            add zero
                                                                                                                m_n =
                                                                                                              add zero
                                                                                                                m_n →
                                                                                                            add zero
                                                                                                                m_n =
                                                                                                              m_n),
                                                                                                            a
                                                                                                              (eq.refl
                                                                                                                 (add
                                                                                                                    zero
                                                                                                                    m_n)))
                                                                                                         h
                                                                                                         h
                                                                                                         (λ
                                                                                                          (n_eq :
                                                                                                            add zero
                                                                                                                m_n =
                                                                                                              m_n),
                                                                                                            n_eq),
                                                                                               mpr := λ
                                                                                                      (a :
                                                                                                        add zero m_n =
                                                                                                          m_n),
                                                                                                        eq.rec
                                                                                                          (eq.refl
                                                                                                             (succ
                                                                                                                (add
                                                                                                                   zero
                                                                                                                   m_n)))
                                                                                                          a}))))
                                                                                n)
                                                                             (eq.rec
                                                                                (eq.refl (succ (add zero n) = succ n))
                                                                                (eq.rec
                                                                                   (eq.refl
                                                                                      (succ (add zero n) = succ n))
                                                                                   (propext
                                                                                      {mp := λ
                                                                                             (h :
                                                                                               succ (add zero n) =
                                                                                                 succ n),
                                                                                               eq.rec
                                                                                                 (λ
                                                                                                  (h11 :
                                                                                                    succ (add zero n) =
                                                                                                      succ (add zero n))
                                                                                                  (a :
                                                                                                    add zero n =
                                                                                                      add zero n →
                                                                                                    add zero n = n),
                                                                                                    a
                                                                                                      (eq.refl
                                                                                                         (add zero n)))
                                                                                                 h
                                                                                                 h
                                                                                                 (λ
                                                                                                  (n_eq :
                                                                                                    add zero n = n),
                                                                                                    n_eq),
                                                                                       mpr := λ (a : add zero n = n),
                                                                                                eq.rec
                                                                                                  (eq.refl
                                                                                                     (succ
                                                                                                        (add zero n)))
                                                                                                  a}))))))
                                                                    (propext
                                                                       {mp := λ (hl : succ n = succ n), true.intro,
                                                                        mpr := λ (hr : true), eq.refl (succ n)}))))
                                                           (λ (n_n : mynat)
                                                            (n_ih : add (succ n) n_n = succ (add n_n n)),
                                                              eq.rec n_ih
                                                                (eq.rec
                                                                   (eq.refl
                                                                      (succ (add (succ n) n_n) =
                                                                         succ (add (succ n_n) n)))
                                                                   (eq.rec
                                                                      (eq.rec
                                                                         (eq.refl
                                                                            (succ (add (succ n) n_n) =
                                                                               succ (add (succ n_n) n)))
                                                                         (eq.rec
                                                                            (mynat.rec (eq.refl (succ n_n))
                                                                               (λ (n_n_1 : mynat)
                                                                                (n_ih :
                                                                                  add (succ n_n) n_n_1 =
                                                                                    succ (add n_n n_n_1)),
                                                                                  eq.rec n_ih
                                                                                    (eq.rec
                                                                                       (eq.refl
                                                                                          (succ (add (succ n_n) n_n_1) =
                                                                                             succ
                                                                                               (succ (add n_n n_n_1))))
                                                                                       (eq.rec
                                                                                          (eq.refl
                                                                                             (succ
                                                                                                  (add (succ n_n)
                                                                                                     n_n_1) =
                                                                                                succ
                                                                                                  (succ
                                                                                                     (add n_n n_n_1))))
                                                                                          (propext
                                                                                             {mp := λ
                                                                                                    (h :
                                                                                                      succ
                                                                                                          (add
                                                                                                             (succ n_n)
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
                                                                                                                  (succ
                                                                                                                     n_n)
                                                                                                                  n_n_1) =
                                                                                                             succ
                                                                                                               (add
                                                                                                                  (succ
                                                                                                                     n_n)
                                                                                                                  n_n_1))
                                                                                                         (a :
                                                                                                           add
                                                                                                               (succ
                                                                                                                  n_n)
                                                                                                               n_n_1 =
                                                                                                             add
                                                                                                               (succ
                                                                                                                  n_n)
                                                                                                               n_n_1 →
                                                                                                           add
                                                                                                               (succ
                                                                                                                  n_n)
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
                                                                                                           add
                                                                                                               (succ
                                                                                                                  n_n)
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
                                                                                                           (add n_n
                                                                                                              n_n_1)),
                                                                                                       eq.rec
                                                                                                         (eq.refl
                                                                                                            (succ
                                                                                                               (add
                                                                                                                  (succ
                                                                                                                     n_n)
                                                                                                                  n_n_1)))
                                                                                                         a}))))
                                                                               n)
                                                                            (eq.rec
                                                                               (eq.refl
                                                                                  (succ (add (succ n_n) n) =
                                                                                     succ (succ (add n_n n))))
                                                                               (eq.rec
                                                                                  (eq.refl
                                                                                     (succ (add (succ n_n) n) =
                                                                                        succ (succ (add n_n n))))
                                                                                  (propext
                                                                                     {mp := λ
                                                                                            (h :
                                                                                              succ (add (succ n_n) n) =
                                                                                                succ
                                                                                                  (succ (add n_n n))),
                                                                                              eq.rec
                                                                                                (λ
                                                                                                 (h11 :
                                                                                                   succ
                                                                                                       (add (succ n_n)
                                                                                                          n) =
                                                                                                     succ
                                                                                                       (add (succ n_n)
                                                                                                          n))
                                                                                                 (a :
                                                                                                   add (succ n_n) n =
                                                                                                     add (succ n_n)
                                                                                                       n →
                                                                                                   add (succ n_n) n =
                                                                                                     succ (add n_n n)),
                                                                                                   a
                                                                                                     (eq.refl
                                                                                                        (add (succ n_n)
                                                                                                           n)))
                                                                                                h
                                                                                                h
                                                                                                (λ
                                                                                                 (n_eq :
                                                                                                   add (succ n_n) n =
                                                                                                     succ (add n_n n)),
                                                                                                   n_eq),
                                                                                      mpr := λ
                                                                                             (a :
                                                                                               add (succ n_n) n =
                                                                                                 succ (add n_n n)),
                                                                                               eq.rec
                                                                                                 (eq.refl
                                                                                                    (succ
                                                                                                       (add (succ n_n)
                                                                                                          n)))
                                                                                                 a})))))
                                                                      (propext
                                                                         {mp := λ
                                                                                (h :
                                                                                  succ (add (succ n) n_n) =
                                                                                    succ (succ (add n_n n))),
                                                                                  eq.rec
                                                                                    (λ
                                                                                     (h11 :
                                                                                       succ (add (succ n) n_n) =
                                                                                         succ (add (succ n) n_n))
                                                                                     (a :
                                                                                       add (succ n) n_n =
                                                                                         add (succ n) n_n →
                                                                                       add (succ n) n_n =
                                                                                         succ (add n_n n)),
                                                                                       a (eq.refl (add (succ n) n_n)))
                                                                                    h
                                                                                    h
                                                                                    (λ
                                                                                     (n_eq :
                                                                                       add (succ n) n_n =
                                                                                         succ (add n_n n)), n_eq),
                                                                          mpr := λ
                                                                                 (a :
                                                                                   add (succ n) n_n = succ (add n_n n)),
                                                                                   eq.rec
                                                                                     (eq.refl (succ (add (succ n) n_n)))
                                                                                     a}))))
                                                           w)))).mp
                                                 ha)})))
                       M
                       (eq.rec (eq.refl zero) h))
                  hMl0
                  hMl0))))
    (λ (N_n : mynat) (N_ih : ∀ (M : mynat), (∃ (k : mynat), N_n = add M k) → statement M) (M : mynat)
     (hMlesN : ∃ (k : mynat), succ N_n = add M k),
       Exists.rec
         (λ (w : mynat) (h : succ N_n = add M w) («_» : ∃ (k : mynat), succ N_n = add M k),
            mynat.rec
              (λ (hd : succ N_n = M),
                 eq.rec (inductive_step N_n N_ih)
                   (eq.rec (eq.refl (statement M)) (eq.rec (eq.refl (statement M)) (eq.rec (eq.refl (succ N_n)) hd))))
              (λ (n : mynat) (ih : succ N_n = add M n → statement M) (hd : succ N_n = succ (add M n)),
                 N_ih M
                   (Exists.intro n
                      (eq.rec hd
                         (eq.rec (eq.refl (succ N_n = succ (add M n)))
                            (propext
                               {mp := λ (h : succ N_n = succ (add M n)),
                                        eq.rec
                                          (λ (h11 : succ N_n = succ N_n) (a : N_n = N_n → N_n = add M n),
                                             a (eq.refl N_n))
                                          h
                                          h
                                          (λ (n_eq : N_n = add M n), n_eq),
                                mpr := λ (a : N_n = add M n), eq.rec (eq.refl (succ N_n)) a})))))
              w
              h)
         hMlesN
         hMlesN)
    k
    k
    (Exists.intro zero
       (eq.rec (eq.refl (succ k))
          (eq.rec (eq.refl (succ k = succ k))
             (propext {mp := λ (h : succ k = succ k), eq.refl k, mpr := λ (a : k = k), eq.refl (succ k)}))))
