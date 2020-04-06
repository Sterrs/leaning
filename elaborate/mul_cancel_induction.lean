mynat.rec
  (λ {m k : mynat} (hmn0 : m = zero → false) (hmk0 : zero = mul m k),
     eq.rec (eq.refl k)
       (mynat.rec
          (eq.rec true.intro
             (eq.rec (eq.refl ((m = zero → false) → zero = zero → zero = zero))
                (eq.rec
                   (propext
                      {mp := λ (hab : (m = zero → false) → zero = zero → zero = zero) (hc : m = zero → false),
                               (eq.rec
                                  {mp := λ (h : zero = zero → zero = zero), h,
                                   mpr := λ (h : zero = zero → zero = zero), h}
                                  (eq.rec
                                     (propext
                                        {mp := λ (hab : zero = zero → zero = zero) (hc : true),
                                                 (eq.rec {mp := λ (h : zero = zero), h, mpr := λ (h : zero = zero), h}
                                                    (eq.rec (eq.refl (zero = zero))
                                                       (propext
                                                          {mp := λ (hl : zero = zero), true.intro,
                                                           mpr := λ (hr : true), eq.refl zero}))).mp
                                                   (hab
                                                      ((eq.rec
                                                          {mp := λ (h : zero = zero), h,
                                                           mpr := λ (h : zero = zero), h}
                                                          (eq.rec (eq.refl (zero = zero))
                                                             (propext
                                                                {mp := λ (hl : zero = zero), true.intro,
                                                                 mpr := λ (hr : true), eq.refl zero}))).mpr
                                                         hc)),
                                         mpr := λ (hcd : true → true) (ha : zero = zero),
                                                  (eq.rec
                                                     {mp := λ (h : zero = zero), h, mpr := λ (h : zero = zero), h}
                                                     (eq.rec (eq.refl (zero = zero))
                                                        (propext
                                                           {mp := λ (hl : zero = zero), true.intro,
                                                            mpr := λ (hr : true), eq.refl zero}))).mpr
                                                    (hcd
                                                       ((eq.rec
                                                           {mp := λ (h : zero = zero), h,
                                                            mpr := λ (h : zero = zero), h}
                                                           (eq.rec (eq.refl (zero = zero))
                                                              (propext
                                                                 {mp := λ (hl : zero = zero), true.intro,
                                                                  mpr := λ (hr : true), eq.refl zero}))).mp
                                                          ha))})
                                     (propext
                                        {mp := λ (h : true → true), h true.intro, mpr := λ (h h' : true), h}))).mp
                                 (hab hc),
                       mpr := λ (hcd : (m = zero → false) → true) (ha : m = zero → false),
                                (eq.rec
                                   {mp := λ (h : zero = zero → zero = zero), h,
                                    mpr := λ (h : zero = zero → zero = zero), h}
                                   (eq.rec
                                      (propext
                                         {mp := λ (hab : zero = zero → zero = zero) (hc : true),
                                                  (eq.rec
                                                     {mp := λ (h : zero = zero), h, mpr := λ (h : zero = zero), h}
                                                     (eq.rec (eq.refl (zero = zero))
                                                        (propext
                                                           {mp := λ (hl : zero = zero), true.intro,
                                                            mpr := λ (hr : true), eq.refl zero}))).mp
                                                    (hab
                                                       ((eq.rec
                                                           {mp := λ (h : zero = zero), h,
                                                            mpr := λ (h : zero = zero), h}
                                                           (eq.rec (eq.refl (zero = zero))
                                                              (propext
                                                                 {mp := λ (hl : zero = zero), true.intro,
                                                                  mpr := λ (hr : true), eq.refl zero}))).mpr
                                                          hc)),
                                          mpr := λ (hcd : true → true) (ha : zero = zero),
                                                   (eq.rec
                                                      {mp := λ (h : zero = zero), h, mpr := λ (h : zero = zero), h}
                                                      (eq.rec (eq.refl (zero = zero))
                                                         (propext
                                                            {mp := λ (hl : zero = zero), true.intro,
                                                             mpr := λ (hr : true), eq.refl zero}))).mpr
                                                     (hcd
                                                        ((eq.rec
                                                            {mp := λ (h : zero = zero), h,
                                                             mpr := λ (h : zero = zero), h}
                                                            (eq.rec (eq.refl (zero = zero))
                                                               (propext
                                                                  {mp := λ (hl : zero = zero), true.intro,
                                                                   mpr := λ (hr : true), eq.refl zero}))).mp
                                                           ha))})
                                      (propext
                                         {mp := λ (h : true → true), h true.intro, mpr := λ (h h' : true), h}))).mpr
                                  (hcd ha)})
                   (propext
                      {mp := λ (h : (m = zero → false) → true), true.intro,
                       mpr := λ (ha : true) (h : m = zero → false), true.intro}))))
          (λ (n : mynat) (ih : (m = zero → false) → mul m n = zero → n = zero) (hmne0 : m = zero → false)
           (hmn0 : add m (mul m n) = zero),
             false.rec (succ n = zero)
               (hmne0
                  (mynat.rec
                     (eq.rec true.intro
                        (eq.rec (eq.refl (add zero (mul m n) = zero → zero = zero))
                           (eq.rec
                              (propext
                                 {mp := λ (hab : add zero (mul m n) = zero → zero = zero) (hc : mul m n = zero),
                                          (eq.rec {mp := λ (h : zero = zero), h, mpr := λ (h : zero = zero), h}
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
                                                            ((mynat.rec
                                                                ⟨λ (m : mynat),
                                                                   eq.rec (eq.refl m)
                                                                     (eq.rec (eq.refl (m = add zero m))
                                                                        (eq.rec (eq.refl (m = add zero m))
                                                                           ((mynat.rec ⟨eq.refl zero, punit.star⟩
                                                                               (λ (n : mynat)
                                                                                (ih :
                                                                                  pprod (add zero n = n)
                                                                                    (mynat.rec punit
                                                                                       (λ (n : mynat) (ih : Type),
                                                                                          pprod
                                                                                            (pprod (add zero n = n) ih)
                                                                                            punit)
                                                                                       n)),
                                                                                  ⟨eq.rec (eq.refl (succ n))
                                                                                     (eq.rec
                                                                                        (eq.refl
                                                                                           (succ (add zero n) = succ n))
                                                                                        (eq.rec
                                                                                           (eq.refl
                                                                                              (succ (add zero n) =
                                                                                                 succ n))
                                                                                           (ih.fst))),
                                                                                   ⟨ih, punit.star⟩⟩)
                                                                               m).fst))),
                                                                 punit.star⟩
                                                                (λ (n : mynat)
                                                                 (ih :
                                                                   pprod (∀ (m : mynat), add m n = add n m)
                                                                     (mynat.rec punit
                                                                        (λ (n : mynat) (ih : Type),
                                                                           pprod
                                                                             (pprod (∀ (m : mynat), add m n = add n m)
                                                                                ih)
                                                                             punit)
                                                                        n)),
                                                                   ⟨λ (m : mynat),
                                                                      eq.rec
                                                                        (eq.rec (eq.refl (succ (add n m)))
                                                                           (eq.rec
                                                                              (eq.refl
                                                                                 (succ (add m n) = succ (add n m)))
                                                                              (eq.rec
                                                                                 (eq.refl
                                                                                    (succ (add m n) = succ (add n m)))
                                                                                 (ih.fst m))))
                                                                        (eq.rec
                                                                           (eq.refl (succ (add m n) = add (succ n) m))
                                                                           (eq.rec
                                                                              (eq.refl
                                                                                 (succ (add m n) = add (succ n) m))
                                                                              ((mynat.rec
                                                                                  ⟨λ (m : mynat), eq.refl (succ m),
                                                                                   punit.star⟩
                                                                                  (λ (n : mynat)
                                                                                   (ih :
                                                                                     pprod
                                                                                       (∀ (m : mynat),
                                                                                          add (succ m) n =
                                                                                            succ (add m n))
                                                                                       (mynat.rec punit
                                                                                          (λ (n : mynat) (ih : Type),
                                                                                             pprod
                                                                                               (pprod
                                                                                                  (∀ (m : mynat),
                                                                                                     add (succ m) n =
                                                                                                       succ (add m n))
                                                                                                  ih)
                                                                                               punit)
                                                                                          n)),
                                                                                     ⟨λ (m : mynat),
                                                                                        eq.rec
                                                                                          (eq.refl
                                                                                             (succ (succ (add m n))))
                                                                                          (eq.rec
                                                                                             (eq.refl
                                                                                                (succ (add (succ m) n) =
                                                                                                   succ
                                                                                                     (succ (add m n))))
                                                                                             (eq.rec
                                                                                                (eq.refl
                                                                                                   (succ
                                                                                                        (add (succ m)
                                                                                                           n) =
                                                                                                      succ
                                                                                                        (succ
                                                                                                           (add m n))))
                                                                                                (ih.fst m))),
                                                                                      ⟨ih, punit.star⟩⟩)
                                                                                  m).fst
                                                                                 n))),
                                                                    ⟨ih, punit.star⟩⟩)
                                                                (mul m n)).fst
                                                               zero))))).mpr
                                                  hc)),
                                  mpr := λ (hcd : mul m n = zero → true) (ha : add zero (mul m n) = zero),
                                           (eq.rec {mp := λ (h : zero = zero), h, mpr := λ (h : zero = zero), h}
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
                                                             ((mynat.rec
                                                                 ⟨λ (m : mynat),
                                                                    eq.rec (eq.refl m)
                                                                      (eq.rec (eq.refl (m = add zero m))
                                                                         (eq.rec (eq.refl (m = add zero m))
                                                                            ((mynat.rec ⟨eq.refl zero, punit.star⟩
                                                                                (λ (n : mynat)
                                                                                 (ih :
                                                                                   pprod (add zero n = n)
                                                                                     (mynat.rec punit
                                                                                        (λ (n : mynat) (ih : Type),
                                                                                           pprod
                                                                                             (pprod (add zero n = n) ih)
                                                                                             punit)
                                                                                        n)),
                                                                                   ⟨eq.rec (eq.refl (succ n))
                                                                                      (eq.rec
                                                                                         (eq.refl
                                                                                            (succ (add zero n) =
                                                                                               succ n))
                                                                                         (eq.rec
                                                                                            (eq.refl
                                                                                               (succ (add zero n) =
                                                                                                  succ n))
                                                                                            (ih.fst))),
                                                                                    ⟨ih, punit.star⟩⟩)
                                                                                m).fst))),
                                                                  punit.star⟩
                                                                 (λ (n : mynat)
                                                                  (ih :
                                                                    pprod (∀ (m : mynat), add m n = add n m)
                                                                      (mynat.rec punit
                                                                         (λ (n : mynat) (ih : Type),
                                                                            pprod
                                                                              (pprod
                                                                                 (∀ (m : mynat), add m n = add n m)
                                                                                 ih)
                                                                              punit)
                                                                         n)),
                                                                    ⟨λ (m : mynat),
                                                                       eq.rec
                                                                         (eq.rec (eq.refl (succ (add n m)))
                                                                            (eq.rec
                                                                               (eq.refl
                                                                                  (succ (add m n) = succ (add n m)))
                                                                               (eq.rec
                                                                                  (eq.refl
                                                                                     (succ (add m n) = succ (add n m)))
                                                                                  (ih.fst m))))
                                                                         (eq.rec
                                                                            (eq.refl (succ (add m n) = add (succ n) m))
                                                                            (eq.rec
                                                                               (eq.refl
                                                                                  (succ (add m n) = add (succ n) m))
                                                                               ((mynat.rec
                                                                                   ⟨λ (m : mynat), eq.refl (succ m),
                                                                                    punit.star⟩
                                                                                   (λ (n : mynat)
                                                                                    (ih :
                                                                                      pprod
                                                                                        (∀ (m : mynat),
                                                                                           add (succ m) n =
                                                                                             succ (add m n))
                                                                                        (mynat.rec punit
                                                                                           (λ (n : mynat) (ih : Type),
                                                                                              pprod
                                                                                                (pprod
                                                                                                   (∀ (m : mynat),
                                                                                                      add (succ m) n =
                                                                                                        succ (add m n))
                                                                                                   ih)
                                                                                                punit)
                                                                                           n)),
                                                                                      ⟨λ (m : mynat),
                                                                                         eq.rec
                                                                                           (eq.refl
                                                                                              (succ (succ (add m n))))
                                                                                           (eq.rec
                                                                                              (eq.refl
                                                                                                 (succ
                                                                                                      (add (succ m) n) =
                                                                                                    succ
                                                                                                      (succ (add m n))))
                                                                                              (eq.rec
                                                                                                 (eq.refl
                                                                                                    (succ
                                                                                                         (add (succ m)
                                                                                                            n) =
                                                                                                       succ
                                                                                                         (succ
                                                                                                            (add m n))))
                                                                                                 (ih.fst m))),
                                                                                       ⟨ih, punit.star⟩⟩)
                                                                                   m).fst
                                                                                  n))),
                                                                     ⟨ih, punit.star⟩⟩)
                                                                 (mul m n)).fst
                                                                zero))))).mp
                                                   ha))})
                              (propext
                                 {mp := λ (h : mul m n = zero → true), true.intro,
                                  mpr := λ (ha : true) (h : mul m n = zero), true.intro}))))
                     (λ (n_1 : mynat) (ih : add n_1 (mul m n) = zero → n_1 = zero),
                        eq.rec
                          (λ (h : succ (add n_1 (mul m n)) = zero),
                             false.rec (succ n_1 = zero)
                               (eq.rec
                                  (λ («_» : succ (add n_1 (mul m n)) = succ (add n_1 (mul m n)))
                                   (a : zero = succ (add n_1 (mul m n))),
                                     eq.rec
                                       (λ (h11 : zero = zero) (a : h == eq.refl (succ (add n_1 (mul m n))) → false),
                                          a)
                                       a
                                       a)
                                  h
                                  h
                                  (eq.refl zero)
                                  (heq.refl h)))
                          (eq.rec (eq.refl (add (succ n_1) (mul m n) = zero → succ n_1 = zero))
                             (eq.rec (eq.refl (add (succ n_1) (mul m n) = zero → succ n_1 = zero))
                                ((mynat.rec ⟨λ (m : mynat), eq.refl (succ m), punit.star⟩
                                    (λ (n : mynat)
                                     (ih :
                                       pprod (∀ (m : mynat), add (succ m) n = succ (add m n))
                                         (mynat.rec punit
                                            (λ (n : mynat) (ih : Type),
                                               pprod (pprod (∀ (m : mynat), add (succ m) n = succ (add m n)) ih)
                                                 punit)
                                            n)),
                                       ⟨λ (m : mynat),
                                          eq.rec (eq.refl (succ (succ (add m n))))
                                            (eq.rec (eq.refl (succ (add (succ m) n) = succ (succ (add m n))))
                                               (eq.rec (eq.refl (succ (add (succ m) n) = succ (succ (add m n))))
                                                  (ih.fst m))),
                                        ⟨ih, punit.star⟩⟩)
                                    (mul m n)).fst
                                   n_1))))
                     m
                     hmn0)))
          k
          hmn0
          (eq.rec (eq.refl zero) hmk0)))
  (λ (n : mynat) (hn : ∀ {m k : mynat}, (m = zero → false) → mul m n = mul m k → n = k) {m k : mynat}
   (hmn0 : m = zero → false) (heq_1 : add m (mul m n) = mul m k),
     mynat.rec
       (λ (heq_1 : add m (mul m n) = zero),
          false.rec (succ n = zero)
            (eq.rec
               (λ («_» : succ n = succ n) (a : zero = succ n),
                  eq.rec
                    (λ (h11 : zero = zero)
                     (a :
                       false.rec (succ n = zero)
                           (hmn0
                              (mynat.rec
                                 (eq.rec true.intro
                                    (eq.rec (eq.refl (add zero (mul m n) = zero → zero = zero))
                                       (eq.rec
                                          (propext
                                             {mp := λ (hab : add zero (mul m n) = zero → zero = zero)
                                                    (hc : mul m n = zero),
                                                      (eq.rec
                                                         {mp := λ (h : zero = zero), h, mpr := λ (h : zero = zero), h}
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
                                                                        ((mynat.rec
                                                                            ⟨λ (m : mynat),
                                                                               eq.rec (eq.refl m)
                                                                                 (eq.rec (eq.refl (m = add zero m))
                                                                                    (eq.rec (eq.refl (m = add zero m))
                                                                                       ((mynat.rec
                                                                                           ⟨eq.refl zero,
                                                                                            punit.star⟩
                                                                                           (λ (n : mynat)
                                                                                            (ih :
                                                                                              pprod (add zero n = n)
                                                                                                (mynat.rec punit
                                                                                                   (λ (n : mynat)
                                                                                                    (ih : Type),
                                                                                                      pprod
                                                                                                        (pprod … ih)
                                                                                                        punit)
                                                                                                   n)),
                                                                                              ⟨eq.rec
                                                                                                 (eq.refl (succ n))
                                                                                                 (eq.rec
                                                                                                    (eq.refl
                                                                                                       (succ (… n) =
                                                                                                          succ n))
                                                                                                    (eq.rec
                                                                                                       (eq.refl
                                                                                                          (succ … =
                                                                                                             succ n))
                                                                                                       (ih.fst))),
                                                                                               ⟨ih, punit.star⟩⟩)
                                                                                           m).fst))),
                                                                             punit.star⟩
                                                                            (λ (n : mynat)
                                                                             (ih :
                                                                               pprod
                                                                                 (∀ (m : mynat), add m n = add n m)
                                                                                 (mynat.rec punit
                                                                                    (λ (n : mynat) (ih : Type),
                                                                                       pprod
                                                                                         (pprod
                                                                                            (∀ (m : mynat),
                                                                                               add m n = add n m)
                                                                                            ih)
                                                                                         punit)
                                                                                    n)),
                                                                               ⟨λ (m : mynat),
                                                                                  eq.rec
                                                                                    (eq.rec (eq.refl (succ (add n m)))
                                                                                       (eq.rec
                                                                                          (eq.refl
                                                                                             (succ (add m n) =
                                                                                                succ (add n m)))
                                                                                          (eq.rec
                                                                                             (eq.refl
                                                                                                (succ (add m n) =
                                                                                                   succ (add n m)))
                                                                                             (ih.fst m))))
                                                                                    (eq.rec
                                                                                       (eq.refl
                                                                                          (succ (add m n) =
                                                                                             add (succ n) m))
                                                                                       (eq.rec
                                                                                          (eq.refl
                                                                                             (succ (add m n) =
                                                                                                add (succ n) m))
                                                                                          ((mynat.rec
                                                                                              ⟨λ (m : mynat),
                                                                                                 eq.refl (succ m),
                                                                                               punit.star⟩
                                                                                              (λ (n : mynat)
                                                                                               (ih :
                                                                                                 pprod
                                                                                                   (∀ (m : mynat),
                                                                                                      add (succ m) n =
                                                                                                        succ (add m n))
                                                                                                   (mynat.rec punit
                                                                                                      (λ (n : mynat)
                                                                                                       (ih : Type),
                                                                                                         pprod (… ih)
                                                                                                           punit)
                                                                                                      n)),
                                                                                                 ⟨λ (m : mynat),
                                                                                                    eq.rec
                                                                                                      (eq.refl
                                                                                                         (succ
                                                                                                            (succ …)))
                                                                                                      (eq.rec
                                                                                                         (eq.refl
                                                                                                            (… = …))
                                                                                                         (eq.rec
                                                                                                            (eq.refl
                                                                                                               …)
                                                                                                            (ih.fst
                                                                                                               m))),
                                                                                                  ⟨ih,
                                                                                                   punit.star⟩⟩)
                                                                                              m).fst
                                                                                             n))),
                                                                                ⟨ih, punit.star⟩⟩)
                                                                            (mul m n)).fst
                                                                           zero))))).mpr
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
                                                                         ((mynat.rec
                                                                             ⟨λ (m : mynat),
                                                                                eq.rec (eq.refl m)
                                                                                  (eq.rec (eq.refl (m = add zero m))
                                                                                     (eq.rec (eq.refl (m = add zero m))
                                                                                        ((mynat.rec
                                                                                            ⟨eq.refl zero,
                                                                                             punit.star⟩
                                                                                            (λ (n : mynat)
                                                                                             (ih :
                                                                                               pprod (add zero n = n)
                                                                                                 (mynat.rec punit
                                                                                                    (λ (n : mynat)
                                                                                                     (ih : Type),
                                                                                                       pprod
                                                                                                         (pprod … ih)
                                                                                                         punit)
                                                                                                    n)),
                                                                                               ⟨eq.rec
                                                                                                  (eq.refl (succ n))
                                                                                                  (eq.rec
                                                                                                     (eq.refl
                                                                                                        (succ (… n) =
                                                                                                           succ n))
                                                                                                     (eq.rec
                                                                                                        (eq.refl
                                                                                                           (succ … =
                                                                                                              succ n))
                                                                                                        (ih.fst))),
                                                                                                ⟨ih, punit.star⟩⟩)
                                                                                            m).fst))),
                                                                              punit.star⟩
                                                                             (λ (n : mynat)
                                                                              (ih :
                                                                                pprod
                                                                                  (∀ (m : mynat), add m n = add n m)
                                                                                  (mynat.rec punit
                                                                                     (λ (n : mynat) (ih : Type),
                                                                                        pprod
                                                                                          (pprod
                                                                                             (∀ (m : mynat),
                                                                                                add m n = add n m)
                                                                                             ih)
                                                                                          punit)
                                                                                     n)),
                                                                                ⟨λ (m : mynat),
                                                                                   eq.rec
                                                                                     (eq.rec (eq.refl (succ (add n m)))
                                                                                        (eq.rec
                                                                                           (eq.refl
                                                                                              (succ (add m n) =
                                                                                                 succ (add n m)))
                                                                                           (eq.rec
                                                                                              (eq.refl
                                                                                                 (succ (add m n) =
                                                                                                    succ (add n m)))
                                                                                              (ih.fst m))))
                                                                                     (eq.rec
                                                                                        (eq.refl
                                                                                           (succ (add m n) =
                                                                                              add (succ n) m))
                                                                                        (eq.rec
                                                                                           (eq.refl
                                                                                              (succ (add m n) =
                                                                                                 add (succ n) m))
                                                                                           ((mynat.rec
                                                                                               ⟨λ (m : mynat),
                                                                                                  eq.refl (succ m),
                                                                                                punit.star⟩
                                                                                               (λ (n : mynat)
                                                                                                (ih :
                                                                                                  pprod
                                                                                                    (∀ (m : mynat),
                                                                                                       add (succ m) n =
                                                                                                         succ (add m n))
                                                                                                    (mynat.rec punit
                                                                                                       (λ (n : mynat)
                                                                                                        (ih : Type),
                                                                                                          pprod (… ih)
                                                                                                            punit)
                                                                                                       n)),
                                                                                                  ⟨λ (m : mynat),
                                                                                                     eq.rec
                                                                                                       (eq.refl
                                                                                                          (succ
                                                                                                             (succ
                                                                                                                …)))
                                                                                                       (eq.rec
                                                                                                          (eq.refl
                                                                                                             (… =
                                                                                                                …))
                                                                                                          (eq.rec
                                                                                                             (eq.refl
                                                                                                                …)
                                                                                                             (ih.fst
                                                                                                                m))),
                                                                                                   ⟨ih,
                                                                                                    punit.star⟩⟩)
                                                                                               m).fst
                                                                                              n))),
                                                                                 ⟨ih, punit.star⟩⟩)
                                                                             (mul m n)).fst
                                                                            zero))))).mp
                                                               ha))})
                                          (propext
                                             {mp := λ (h : mul m n = zero → true), true.intro,
                                              mpr := λ (ha : true) (h : mul m n = zero), true.intro}))))
                                 (λ (n_1 : mynat) (ih : add n_1 (mul m n) = zero → n_1 = zero),
                                    eq.rec
                                      (λ (h : succ (add n_1 (mul m n)) = zero),
                                         false.rec (succ n_1 = zero)
                                           (eq.rec
                                              (λ («_» : succ (add n_1 (mul m n)) = succ (add n_1 (mul m n)))
                                               (a : zero = succ (add n_1 (mul m n))),
                                                 eq.rec
                                                   (λ (h11 : zero = zero)
                                                    (a : h == eq.refl (succ (add n_1 (mul m n))) → false), a)
                                                   a
                                                   a)
                                              h
                                              h
                                              (eq.refl zero)
                                              (heq.refl h)))
                                      (eq.rec (eq.refl (add (succ n_1) (mul m n) = zero → succ n_1 = zero))
                                         (eq.rec (eq.refl (add (succ n_1) (mul m n) = zero → succ n_1 = zero))
                                            ((mynat.rec ⟨λ (m : mynat), eq.refl (succ m), punit.star⟩
                                                (λ (n : mynat)
                                                 (ih :
                                                   pprod (∀ (m : mynat), add (succ m) n = succ (add m n))
                                                     (mynat.rec punit
                                                        (λ (n : mynat) (ih : Type),
                                                           pprod
                                                             (pprod (∀ (m : mynat), add (succ m) n = succ (add m n))
                                                                ih)
                                                             punit)
                                                        n)),
                                                   ⟨λ (m : mynat),
                                                      eq.rec (eq.refl (succ (succ (add m n))))
                                                        (eq.rec
                                                           (eq.refl (succ (add (succ m) n) = succ (succ (add m n))))
                                                           (eq.rec
                                                              (eq.refl (succ (add (succ m) n) = succ (succ (add m n))))
                                                              (ih.fst m))),
                                                    ⟨ih, punit.star⟩⟩)
                                                (mul m n)).fst
                                               n_1))))
                                 m
                                 heq_1)) ==
                         eq.refl (succ n) →
                       false), a)
                    a
                    a)
               (false.rec (succ n = zero)
                  (hmn0
                     (mynat.rec
                        (eq.rec true.intro
                           (eq.rec (eq.refl (add zero (mul m n) = zero → zero = zero))
                              (eq.rec
                                 (propext
                                    {mp := λ (hab : add zero (mul m n) = zero → zero = zero) (hc : mul m n = zero),
                                             (eq.rec {mp := λ (h : zero = zero), h, mpr := λ (h : zero = zero), h}
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
                                                               ((mynat.rec
                                                                   ⟨λ (m : mynat),
                                                                      eq.rec (eq.refl m)
                                                                        (eq.rec (eq.refl (m = add zero m))
                                                                           (eq.rec (eq.refl (m = add zero m))
                                                                              ((mynat.rec ⟨eq.refl zero, punit.star⟩
                                                                                  (λ (n : mynat)
                                                                                   (ih :
                                                                                     pprod (add zero n = n)
                                                                                       (mynat.rec punit
                                                                                          (λ (n : mynat) (ih : Type),
                                                                                             pprod
                                                                                               (pprod (add zero n = n)
                                                                                                  ih)
                                                                                               punit)
                                                                                          n)),
                                                                                     ⟨eq.rec (eq.refl (succ n))
                                                                                        (eq.rec
                                                                                           (eq.refl
                                                                                              (succ (add zero n) =
                                                                                                 succ n))
                                                                                           (eq.rec
                                                                                              (eq.refl
                                                                                                 (succ (add zero n) =
                                                                                                    succ n))
                                                                                              (ih.fst))),
                                                                                      ⟨ih, punit.star⟩⟩)
                                                                                  m).fst))),
                                                                    punit.star⟩
                                                                   (λ (n : mynat)
                                                                    (ih :
                                                                      pprod (∀ (m : mynat), add m n = add n m)
                                                                        (mynat.rec punit
                                                                           (λ (n : mynat) (ih : Type),
                                                                              pprod
                                                                                (pprod
                                                                                   (∀ (m : mynat), add m n = add n m)
                                                                                   ih)
                                                                                punit)
                                                                           n)),
                                                                      ⟨λ (m : mynat),
                                                                         eq.rec
                                                                           (eq.rec (eq.refl (succ (add n m)))
                                                                              (eq.rec
                                                                                 (eq.refl
                                                                                    (succ (add m n) = succ (add n m)))
                                                                                 (eq.rec
                                                                                    (eq.refl
                                                                                       (succ (add m n) =
                                                                                          succ (add n m)))
                                                                                    (ih.fst m))))
                                                                           (eq.rec
                                                                              (eq.refl
                                                                                 (succ (add m n) = add (succ n) m))
                                                                              (eq.rec
                                                                                 (eq.refl
                                                                                    (succ (add m n) = add (succ n) m))
                                                                                 ((mynat.rec
                                                                                     ⟨λ (m : mynat),
                                                                                        eq.refl (succ m),
                                                                                      punit.star⟩
                                                                                     (λ (n : mynat)
                                                                                      (ih :
                                                                                        pprod
                                                                                          (∀ (m : mynat),
                                                                                             add (succ m) n =
                                                                                               succ (add m n))
                                                                                          (mynat.rec punit
                                                                                             (λ (n : mynat)
                                                                                              (ih : Type),
                                                                                                pprod
                                                                                                  (pprod
                                                                                                     (∀ (m : mynat),
                                                                                                        add (succ m) n =
                                                                                                          succ
                                                                                                            (add m n))
                                                                                                     ih)
                                                                                                  punit)
                                                                                             n)),
                                                                                        ⟨λ (m : mynat),
                                                                                           eq.rec
                                                                                             (eq.refl
                                                                                                (succ (succ (add m n))))
                                                                                             (eq.rec
                                                                                                (eq.refl
                                                                                                   (succ
                                                                                                        (add (succ m)
                                                                                                           n) =
                                                                                                      succ
                                                                                                        (succ
                                                                                                           (add m n))))
                                                                                                (eq.rec
                                                                                                   (eq.refl
                                                                                                      (succ
                                                                                                           (add (succ m)
                                                                                                              n) =
                                                                                                         succ
                                                                                                           (succ
                                                                                                              (add m
                                                                                                                 n))))
                                                                                                   (ih.fst m))),
                                                                                         ⟨ih, punit.star⟩⟩)
                                                                                     m).fst
                                                                                    n))),
                                                                       ⟨ih, punit.star⟩⟩)
                                                                   (mul m n)).fst
                                                                  zero))))).mpr
                                                     hc)),
                                     mpr := λ (hcd : mul m n = zero → true) (ha : add zero (mul m n) = zero),
                                              (eq.rec {mp := λ (h : zero = zero), h, mpr := λ (h : zero = zero), h}
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
                                                                ((mynat.rec
                                                                    ⟨λ (m : mynat),
                                                                       eq.rec (eq.refl m)
                                                                         (eq.rec (eq.refl (m = add zero m))
                                                                            (eq.rec (eq.refl (m = add zero m))
                                                                               ((mynat.rec
                                                                                   ⟨eq.refl zero, punit.star⟩
                                                                                   (λ (n : mynat)
                                                                                    (ih :
                                                                                      pprod (add zero n = n)
                                                                                        (mynat.rec punit
                                                                                           (λ (n : mynat) (ih : Type),
                                                                                              pprod
                                                                                                (pprod (add zero n = n)
                                                                                                   ih)
                                                                                                punit)
                                                                                           n)),
                                                                                      ⟨eq.rec (eq.refl (succ n))
                                                                                         (eq.rec
                                                                                            (eq.refl
                                                                                               (succ (add zero n) =
                                                                                                  succ n))
                                                                                            (eq.rec
                                                                                               (eq.refl
                                                                                                  (succ (add zero n) =
                                                                                                     succ n))
                                                                                               (ih.fst))),
                                                                                       ⟨ih, punit.star⟩⟩)
                                                                                   m).fst))),
                                                                     punit.star⟩
                                                                    (λ (n : mynat)
                                                                     (ih :
                                                                       pprod (∀ (m : mynat), add m n = add n m)
                                                                         (mynat.rec punit
                                                                            (λ (n : mynat) (ih : Type),
                                                                               pprod
                                                                                 (pprod
                                                                                    (∀ (m : mynat), add m n = add n m)
                                                                                    ih)
                                                                                 punit)
                                                                            n)),
                                                                       ⟨λ (m : mynat),
                                                                          eq.rec
                                                                            (eq.rec (eq.refl (succ (add n m)))
                                                                               (eq.rec
                                                                                  (eq.refl
                                                                                     (succ (add m n) = succ (add n m)))
                                                                                  (eq.rec
                                                                                     (eq.refl
                                                                                        (succ (add m n) =
                                                                                           succ (add n m)))
                                                                                     (ih.fst m))))
                                                                            (eq.rec
                                                                               (eq.refl
                                                                                  (succ (add m n) = add (succ n) m))
                                                                               (eq.rec
                                                                                  (eq.refl
                                                                                     (succ (add m n) = add (succ n) m))
                                                                                  ((mynat.rec
                                                                                      ⟨λ (m : mynat),
                                                                                         eq.refl (succ m),
                                                                                       punit.star⟩
                                                                                      (λ (n : mynat)
                                                                                       (ih :
                                                                                         pprod
                                                                                           (∀ (m : mynat),
                                                                                              add (succ m) n =
                                                                                                succ (add m n))
                                                                                           (mynat.rec punit
                                                                                              (λ (n : mynat)
                                                                                               (ih : Type),
                                                                                                 pprod
                                                                                                   (pprod
                                                                                                      (∀ (m : mynat),
                                                                                                         add (succ m)
                                                                                                             n =
                                                                                                           succ
                                                                                                             (add m n))
                                                                                                      ih)
                                                                                                   punit)
                                                                                              n)),
                                                                                         ⟨λ (m : mynat),
                                                                                            eq.rec
                                                                                              (eq.refl
                                                                                                 (succ
                                                                                                    (succ (add m n))))
                                                                                              (eq.rec
                                                                                                 (eq.refl
                                                                                                    (succ
                                                                                                         (add (succ m)
                                                                                                            n) =
                                                                                                       succ
                                                                                                         (succ
                                                                                                            (add m n))))
                                                                                                 (eq.rec
                                                                                                    (eq.refl
                                                                                                       (succ
                                                                                                            (add
                                                                                                               (succ m)
                                                                                                               n) =
                                                                                                          succ
                                                                                                            (succ
                                                                                                               (add m
                                                                                                                  n))))
                                                                                                    (ih.fst m))),
                                                                                          ⟨ih, punit.star⟩⟩)
                                                                                      m).fst
                                                                                     n))),
                                                                        ⟨ih, punit.star⟩⟩)
                                                                    (mul m n)).fst
                                                                   zero))))).mp
                                                      ha))})
                                 (propext
                                    {mp := λ (h : mul m n = zero → true), true.intro,
                                     mpr := λ (ha : true) (h : mul m n = zero), true.intro}))))
                        (λ (n_1 : mynat) (ih : add n_1 (mul m n) = zero → n_1 = zero),
                           eq.rec
                             (λ (h : succ (add n_1 (mul m n)) = zero),
                                false.rec (succ n_1 = zero)
                                  (eq.rec
                                     (λ («_» : succ (add n_1 (mul m n)) = succ (add n_1 (mul m n)))
                                      (a : zero = succ (add n_1 (mul m n))),
                                        eq.rec
                                          (λ (h11 : zero = zero)
                                           (a : h == eq.refl (succ (add n_1 (mul m n))) → false), a)
                                          a
                                          a)
                                     h
                                     h
                                     (eq.refl zero)
                                     (heq.refl h)))
                             (eq.rec (eq.refl (add (succ n_1) (mul m n) = zero → succ n_1 = zero))
                                (eq.rec (eq.refl …) …)))
                        m
                        heq_1)))
               …
               …
               …))
       …
       k
       heq_1)
  ?M_1
