λ {lst : mylist mynat} (h : lst = empty → false),
  mylist.rec
    (λ (h : empty = empty → false),
       false.rec (false.rec (mylist mynat) (h (eq.refl empty)) ++ false.rec mynat (h (eq.refl empty)) :: empty = empty)
         (h (eq.refl empty)))
    (λ (lst_head : mynat) (lst_tail : mylist mynat)
     (lst_ih : ∀ (h : lst_tail = empty → false), init lst_tail h ++ last lst_tail h :: empty = lst_tail)
     (h : lst_head :: lst_tail = empty → false),
       mylist.rec
         (λ
          (lst_ih :
            ∀ (h : empty = empty → false),
              false.rec (mylist mynat) (h (eq.refl empty)) ++ false.rec mynat (h (eq.refl empty)) :: empty = empty)
          (h : lst_head :: empty = empty → false),
            eq.rec true.intro
              (eq.rec (eq.refl (lst_head :: empty = lst_head :: empty))
                 (eq.rec
                    (eq.rec
                       (eq.rec (eq.refl (lst_head :: empty = lst_head :: empty))
                          (propext
                             {mp := λ (h : lst_head :: empty = lst_head :: empty),
                                      ⟨eq.refl lst_head, eq.refl empty⟩,
                              mpr := λ (a : lst_head = lst_head ∧ empty = empty),
                                       and.rec
                                         (λ (left : lst_head = lst_head) (right : empty = empty)
                                          («_» : lst_head = lst_head ∧ empty = empty), eq.refl (lst_head :: empty))
                                         a
                                         a}))
                       (eq.rec
                          (eq.rec (eq.refl (lst_head = lst_head ∧ empty = empty))
                             (propext
                                {mp := λ (hl : empty = empty), true.intro, mpr := λ (hr : true), eq.refl empty}))
                          (eq.rec (eq.refl (and (lst_head = lst_head)))
                             (propext
                                {mp := λ (hl : lst_head = lst_head), true.intro,
                                 mpr := λ (hr : true), eq.refl lst_head}))))
                    (propext {mp := and.left true, mpr := λ (h : true), ⟨h, h⟩}))))
         (λ (head : mynat) (tail : mylist mynat)
          (ih :
            (∀ (h : tail = empty → false), init tail h ++ last tail h :: empty = tail) →
            ∀ (h : lst_head :: tail = empty → false),
              init (lst_head :: tail) h ++ last (lst_head :: tail) h :: empty = lst_head :: tail)
          (lst_ih :
            ∀ (h : head :: tail = empty → false),
              init (head :: tail) h ++ last (head :: tail) h :: empty = head :: tail)
          (h : lst_head :: head :: tail = empty → false),
            eq.rec
              (lst_ih
                 (λ (h : head :: tail = empty),
                    eq.rec
                      (λ («_» : head :: tail = head :: tail) (H_1 : empty = head :: tail),
                         eq.rec (λ (h11 : empty = empty) (a : h == eq.refl (head :: tail) → false), a) H_1 H_1)
                      h
                      h
                      (eq.refl empty)
                      (heq.refl h)))
              (eq.rec
                 (eq.refl
                    (lst_head ::
                         (init (head :: tail)
                              (λ (h : head :: tail = empty),
                                 eq.rec
                                   (λ («_» : head :: tail = head :: tail) (H_1 : empty = head :: tail),
                                      eq.rec (λ (h11 : empty = empty) (a : h == eq.refl (head :: tail) → false), a)
                                        H_1
                                        H_1)
                                   h
                                   h
                                   (eq.refl empty)
                                   (heq.refl h)) ++
                            last (head :: tail)
                                (λ (h : head :: tail = empty),
                                   eq.rec
                                     (λ («_» : head :: tail = head :: tail) (H_1 : empty = head :: tail),
                                        eq.rec (λ (h11 : empty = empty) (a : h == eq.refl (head :: tail) → false), a)
                                          H_1
                                          H_1)
                                     h
                                     h
                                     (eq.refl empty)
                                     (heq.refl h)) ::
                              empty) =
                       lst_head :: head :: tail))
                 (eq.rec
                    (eq.rec
                       (eq.rec
                          (eq.refl
                             (lst_head ::
                                  (init (head :: tail)
                                       (λ (h : head :: tail = empty),
                                          eq.rec
                                            (λ («_» : head :: tail = head :: tail) (H_1 : empty = head :: tail),
                                               eq.rec
                                                 (λ (h11 : empty = empty) (a : h == eq.refl (head :: tail) → false),
                                                    a)
                                                 H_1
                                                 H_1)
                                            h
                                            h
                                            (eq.refl empty)
                                            (heq.refl h)) ++
                                     last (head :: tail)
                                         (λ (h : head :: tail = empty),
                                            eq.rec
                                              (λ («_» : head :: tail = head :: tail) (H_1 : empty = head :: tail),
                                                 eq.rec
                                                   (λ (h11 : empty = empty)
                                                    (a : h == eq.refl (head :: tail) → false), a)
                                                   H_1
                                                   H_1)
                                              h
                                              h
                                              (eq.refl empty)
                                              (heq.refl h)) ::
                                       empty) =
                                lst_head :: head :: tail))
                          (propext
                             {mp := λ
                                    (h :
                                      lst_head ::
                                          (init (head :: tail)
                                               (λ (h : head :: tail = empty),
                                                  eq.rec
                                                    (λ («_» : head :: tail = head :: tail)
                                                     (H_1 : empty = head :: tail),
                                                       eq.rec
                                                         (λ (h11 : empty = empty)
                                                          (a : h == eq.refl (head :: tail) → false), a)
                                                         H_1
                                                         H_1)
                                                    h
                                                    h
                                                    (eq.refl empty)
                                                    (heq.refl h)) ++
                                             last (head :: tail)
                                                 (λ (h : head :: tail = empty),
                                                    eq.rec
                                                      (λ («_» : head :: tail = head :: tail)
                                                       (H_1 : empty = head :: tail),
                                                         eq.rec
                                                           (λ (h11 : empty = empty)
                                                            (a : h == eq.refl (head :: tail) → false), a)
                                                           H_1
                                                           H_1)
                                                      h
                                                      h
                                                      (eq.refl empty)
                                                      (heq.refl h)) ::
                                               empty) =
                                        lst_head :: head :: tail),
                                      eq.rec
                                        (λ
                                         (h11 :
                                           lst_head ::
                                               (init (head :: tail)
                                                    (λ (h : head :: tail = empty),
                                                       eq.rec
                                                         (λ («_» : head :: tail = head :: tail)
                                                          (H_1 : empty = head :: tail),
                                                            eq.rec
                                                              (λ (h11 : empty = empty)
                                                               (a : h == eq.refl (head :: tail) → false), a)
                                                              H_1
                                                              H_1)
                                                         h
                                                         h
                                                         (eq.refl empty)
                                                         (heq.refl h)) ++
                                                  last (head :: tail)
                                                      (λ (h : head :: tail = empty),
                                                         eq.rec
                                                           (λ («_» : head :: tail = head :: tail)
                                                            (H_1 : empty = head :: tail),
                                                              eq.rec
                                                                (λ (h11 : empty = empty)
                                                                 (a : h == eq.refl (head :: tail) → false), a)
                                                                H_1
                                                                H_1)
                                                           h
                                                           h
                                                           (eq.refl empty)
                                                           (heq.refl h)) ::
                                                    empty) =
                                             lst_head ::
                                               (init (head :: tail)
                                                    (λ (h : head :: tail = empty),
                                                       eq.rec
                                                         (λ («_» : head :: tail = head :: tail)
                                                          (H_1 : empty = head :: tail),
                                                            eq.rec
                                                              (λ (h11 : empty = empty)
                                                               (a : h == eq.refl (head :: tail) → false), a)
                                                              H_1
                                                              H_1)
                                                         h
                                                         h
                                                         (eq.refl empty)
                                                         (heq.refl h)) ++
                                                  last (head :: tail)
                                                      (λ (h : head :: tail = empty),
                                                         eq.rec
                                                           (λ («_» : head :: tail = head :: tail)
                                                            (H_1 : empty = head :: tail),
                                                              eq.rec
                                                                (λ (h11 : empty = empty)
                                                                 (a : h == eq.refl (head :: tail) → false), a)
                                                                H_1
                                                                H_1)
                                                           h
                                                           h
                                                           (eq.refl empty)
                                                           (heq.refl h)) ::
                                                    empty))
                                         (a :
                                           lst_head = lst_head →
                                           init (head :: tail)
                                                 (λ (h : head :: tail = empty),
                                                    eq.rec
                                                      (λ («_» : head :: tail = head :: tail)
                                                       (H_1 : empty = head :: tail),
                                                         eq.rec
                                                           (λ (h11 : empty = empty)
                                                            (a : h == eq.refl (head :: tail) → false), a)
                                                           H_1
                                                           H_1)
                                                      h
                                                      h
                                                      (eq.refl empty)
                                                      (heq.refl h)) ++
                                               last (head :: tail)
                                                   (λ (h : head :: tail = empty),
                                                      eq.rec
                                                        (λ («_» : head :: tail = head :: tail)
                                                         (H_1 : empty = head :: tail),
                                                           eq.rec
                                                             (λ (h11 : empty = empty)
                                                              (a : h == eq.refl (head :: tail) → false), a)
                                                             H_1
                                                             H_1)
                                                        h
                                                        h
                                                        (eq.refl empty)
                                                        (heq.refl h)) ::
                                                 empty =
                                             init (head :: tail)
                                                 (λ (h : head :: tail = empty),
                                                    eq.rec
                                                      (λ («_» : head :: tail = head :: tail)
                                                       (H_1 : empty = head :: tail),
                                                         eq.rec
                                                           (λ (h11 : empty = empty)
                                                            (a : h == eq.refl (head :: tail) → false), a)
                                                           H_1
                                                           H_1)
                                                      h
                                                      h
                                                      (eq.refl empty)
                                                      (heq.refl h)) ++
                                               last (head :: tail)
                                                   (λ (h : head :: tail = empty),
                                                      eq.rec
                                                        (λ («_» : head :: tail = head :: tail)
                                                         (H_1 : empty = head :: tail),
                                                           eq.rec
                                                             (λ (h11 : empty = empty)
                                                              (a : h == eq.refl (head :: tail) → false), a)
                                                             H_1
                                                             H_1)
                                                        h
                                                        h
                                                        (eq.refl empty)
                                                        (heq.refl h)) ::
                                                 empty →
                                           lst_head = lst_head ∧
                                             init (head :: tail)
                                                   (λ (h : head :: tail = empty),
                                                      eq.rec
                                                        (λ («_» : head :: tail = head :: tail)
                                                         (H_1 : empty = head :: tail),
                                                           eq.rec
                                                             (λ (h11 : empty = empty)
                                                              (a : h == eq.refl (head :: tail) → false), a)
                                                             H_1
                                                             H_1)
                                                        h
                                                        h
                                                        (eq.refl empty)
                                                        (heq.refl h)) ++
                                                 last (head :: tail)
                                                     (λ (h : head :: tail = empty),
                                                        eq.rec
                                                          (λ («_» : head :: tail = head :: tail)
                                                           (H_1 : empty = head :: tail),
                                                             eq.rec
                                                               (λ (h11 : empty = empty)
                                                                (a : h == eq.refl (head :: tail) → false), a)
                                                               H_1
                                                               H_1)
                                                          h
                                                          h
                                                          (eq.refl empty)
                                                          (heq.refl h)) ::
                                                   empty =
                                               head :: tail),
                                           a (eq.refl lst_head)
                                             (eq.refl
                                                (init (head :: tail)
                                                     (λ (h : head :: tail = empty),
                                                        eq.rec
                                                          (λ («_» : head :: tail = head :: tail)
                                                           (H_1 : empty = head :: tail),
                                                             eq.rec
                                                               (λ (h11 : empty = empty)
                                                                (a : h == eq.refl (head :: tail) → false), a)
                                                               H_1
                                                               H_1)
                                                          h
                                                          h
                                                          (eq.refl empty)
                                                          (heq.refl h)) ++
                                                   last (head :: tail)
                                                       (λ (h : head :: tail = empty),
                                                          eq.rec
                                                            (λ («_» : head :: tail = head :: tail)
                                                             (H_1 : empty = head :: tail),
                                                               eq.rec
                                                                 (λ (h11 : empty = empty)
                                                                  (a : h == eq.refl (head :: tail) → false), a)
                                                                 H_1
                                                                 H_1)
                                                            h
                                                            h
                                                            (eq.refl empty)
                                                            (heq.refl h)) ::
                                                     empty)))
                                        h
                                        h
                                        (λ (head_eq : lst_head = lst_head)
                                         (tail_eq :
                                           init (head :: tail)
                                                 (λ (h : head :: tail = empty),
                                                    eq.rec
                                                      (λ («_» : head :: tail = head :: tail)
                                                       (H_1 : empty = head :: tail),
                                                         eq.rec
                                                           (λ (h11 : empty = empty)
                                                            (a : h == eq.refl (head :: tail) → false), a)
                                                           H_1
                                                           H_1)
                                                      h
                                                      h
                                                      (eq.refl empty)
                                                      (heq.refl h)) ++
                                               last (head :: tail)
                                                   (λ (h : head :: tail = empty),
                                                      eq.rec
                                                        (λ («_» : head :: tail = head :: tail)
                                                         (H_1 : empty = head :: tail),
                                                           eq.rec
                                                             (λ (h11 : empty = empty)
                                                              (a : h == eq.refl (head :: tail) → false), a)
                                                             H_1
                                                             H_1)
                                                        h
                                                        h
                                                        (eq.refl empty)
                                                        (heq.refl h)) ::
                                                 empty =
                                             head :: tail), ⟨head_eq, tail_eq⟩),
                              mpr := λ
                                     (a :
                                       lst_head = lst_head ∧
                                         init (head :: tail)
                                               (λ (h : head :: tail = empty),
                                                  eq.rec
                                                    (λ («_» : head :: tail = head :: tail)
                                                     (H_1 : empty = head :: tail),
                                                       eq.rec
                                                         (λ (h11 : empty = empty)
                                                          (a : h == eq.refl (head :: tail) → false), a)
                                                         H_1
                                                         H_1)
                                                    h
                                                    h
                                                    (eq.refl empty)
                                                    (heq.refl h)) ++
                                             last (head :: tail)
                                                 (λ (h : head :: tail = empty),
                                                    eq.rec
                                                      (λ («_» : head :: tail = head :: tail)
                                                       (H_1 : empty = head :: tail),
                                                         eq.rec
                                                           (λ (h11 : empty = empty)
                                                            (a : h == eq.refl (head :: tail) → false), a)
                                                           H_1
                                                           H_1)
                                                      h
                                                      h
                                                      (eq.refl empty)
                                                      (heq.refl h)) ::
                                               empty =
                                           head :: tail),
                                       and.rec
                                         (λ (left : lst_head = lst_head)
                                          (right :
                                            init (head :: tail)
                                                  (λ (h : head :: tail = empty),
                                                     eq.rec
                                                       (λ («_» : head :: tail = head :: tail)
                                                        (H_1 : empty = head :: tail),
                                                          eq.rec
                                                            (λ (h11 : empty = empty)
                                                             (a : h == eq.refl (head :: tail) → false), a)
                                                            H_1
                                                            H_1)
                                                       h
                                                       h
                                                       (eq.refl empty)
                                                       (heq.refl h)) ++
                                                last (head :: tail)
                                                    (λ (h : head :: tail = empty),
                                                       eq.rec
                                                         (λ («_» : head :: tail = head :: tail)
                                                          (H_1 : empty = head :: tail),
                                                            eq.rec
                                                              (λ (h11 : empty = empty)
                                                               (a : h == eq.refl (head :: tail) → false), a)
                                                              H_1
                                                              H_1)
                                                         h
                                                         h
                                                         (eq.refl empty)
                                                         (heq.refl h)) ::
                                                  empty =
                                              head :: tail)
                                          («_» :
                                            lst_head = lst_head ∧
                                              init (head :: tail)
                                                    (λ (h : head :: tail = empty),
                                                       eq.rec
                                                         (λ («_» : head :: tail = head :: tail)
                                                          (H_1 : empty = head :: tail),
                                                            eq.rec
                                                              (λ (h11 : empty = empty)
                                                               (a : h == eq.refl (head :: tail) → false), a)
                                                              H_1
                                                              H_1)
                                                         h
                                                         h
                                                         (eq.refl empty)
                                                         (heq.refl h)) ++
                                                  last (head :: tail)
                                                      (λ (h : head :: tail = empty),
                                                         eq.rec
                                                           (λ («_» : head :: tail = head :: tail)
                                                            (H_1 : empty = head :: tail),
                                                              eq.rec
                                                                (λ (h11 : empty = empty)
                                                                 (a : h == eq.refl (head :: tail) → false), a)
                                                                H_1
                                                                H_1)
                                                           h
                                                           h
                                                           (eq.refl empty)
                                                           (heq.refl h)) ::
                                                    empty =
                                                head :: tail),
                                            eq.rec
                                              (eq.refl
                                                 (lst_head ::
                                                    (init (head :: tail)
                                                         (λ (h : head :: tail = empty),
                                                            eq.rec
                                                              (λ («_» : head :: tail = head :: tail)
                                                               (H_1 : empty = head :: tail),
                                                                 eq.rec
                                                                   (λ (h11 : empty = empty)
                                                                    (a : h == eq.refl (head :: tail) → false), a)
                                                                   H_1
                                                                   H_1)
                                                              h
                                                              h
                                                              (eq.refl empty)
                                                              (heq.refl h)) ++
                                                       last (head :: tail)
                                                           (λ (h : head :: tail = empty),
                                                              eq.rec
                                                                (λ («_» : head :: tail = head :: tail)
                                                                 (H_1 : empty = head :: tail),
                                                                   eq.rec
                                                                     (λ (h11 : empty = empty)
                                                                      (a : h == eq.refl (head :: tail) → false), a)
                                                                     H_1
                                                                     H_1)
                                                                h
                                                                h
                                                                (eq.refl empty)
                                                                (heq.refl h)) ::
                                                         empty)))
                                              right)
                                         a
                                         a}))
                       (eq.rec
                          (eq.refl
                             (lst_head = lst_head ∧
                                init (head :: tail)
                                      (λ (h : head :: tail = empty),
                                         eq.rec
                                           (λ («_» : head :: tail = head :: tail) (H_1 : empty = head :: tail),
                                              eq.rec
                                                (λ (h11 : empty = empty) (a : h == eq.refl (head :: tail) → false),
                                                   a)
                                                H_1
                                                H_1)
                                           h
                                           h
                                           (eq.refl empty)
                                           (heq.refl h)) ++
                                    last (head :: tail)
                                        (λ (h : head :: tail = empty),
                                           eq.rec
                                             (λ («_» : head :: tail = head :: tail) (H_1 : empty = head :: tail),
                                                eq.rec
                                                  (λ (h11 : empty = empty) (a : h == eq.refl (head :: tail) → false),
                                                     a)
                                                  H_1
                                                  H_1)
                                             h
                                             h
                                             (eq.refl empty)
                                             (heq.refl h)) ::
                                      empty =
                                  head :: tail))
                          (eq.rec (eq.refl (and (lst_head = lst_head)))
                             (propext
                                {mp := λ (hl : lst_head = lst_head), true.intro,
                                 mpr := λ (hr : true), eq.refl lst_head}))))
                    (propext
                       {mp := and.right
                                (init (head :: tail)
                                       (λ (h : head :: tail = empty),
                                          eq.rec
                                            (λ («_» : head :: tail = head :: tail) (H_1 : empty = head :: tail),
                                               eq.rec
                                                 (λ (h11 : empty = empty) (a : h == eq.refl (head :: tail) → false),
                                                    a)
                                                 H_1
                                                 H_1)
                                            h
                                            h
                                            (eq.refl empty)
                                            (heq.refl h)) ++
                                     last (head :: tail)
                                         (λ (h : head :: tail = empty),
                                            eq.rec
                                              (λ («_» : head :: tail = head :: tail) (H_1 : empty = head :: tail),
                                                 eq.rec
                                                   (λ (h11 : empty = empty)
                                                    (a : h == eq.refl (head :: tail) → false), a)
                                                   H_1
                                                   H_1)
                                              h
                                              h
                                              (eq.refl empty)
                                              (heq.refl h)) ::
                                       empty =
                                   head :: tail),
                        mpr := and.intro true.intro}))))
         lst_tail
         lst_ih
         h)
    lst
    h
