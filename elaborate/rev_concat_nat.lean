λ {lst1 lst2 : mylist mynat},
  mylist.rec
    (eq.rec true.intro
       (eq.rec (eq.refl (rev lst2 = rev lst2 ++ empty))
          (eq.rec
             (eq.rec (eq.refl (rev lst2 = rev lst2 ++ empty))
                (eq.rec (eq.refl (rev lst2 ++ empty))
                   (mylist.rec
                      (eq.rec true.intro
                         (eq.rec (eq.refl (empty = empty))
                            (eq.rec (eq.refl (empty = empty))
                               (propext
                                  {mp := λ (hl : empty = empty), true.intro, mpr := λ (hr : true), eq.refl empty}))))
                      (λ (lst_head : mynat) (lst_tail : mylist mynat) (lst_ih : lst_tail ++ empty = lst_tail),
                         eq.rec true.intro
                           (eq.rec (eq.refl (lst_head :: (lst_tail ++ empty) = lst_head :: lst_tail))
                              (eq.rec
                                 (eq.rec
                                    (eq.rec
                                       (eq.rec (eq.refl (lst_head :: (lst_tail ++ empty) = lst_head :: lst_tail))
                                          (eq.rec (eq.refl (eq (lst_head :: (lst_tail ++ empty))))
                                             (eq.rec (eq.refl (lst_head :: (lst_tail ++ empty)))
                                                (eq.rec (eq.refl (lst_head :: (lst_tail ++ empty))) lst_ih))))
                                       (propext
                                          {mp := λ (h : lst_head :: lst_tail = lst_head :: lst_tail),
                                                   ⟨eq.refl lst_head, eq.refl lst_tail⟩,
                                           mpr := λ (a : lst_head = lst_head ∧ lst_tail = lst_tail),
                                                    and.rec
                                                      (λ (left : lst_head = lst_head) (right : lst_tail = lst_tail)
                                                       («_» : lst_head = lst_head ∧ lst_tail = lst_tail),
                                                         eq.refl (lst_head :: lst_tail))
                                                      a
                                                      a}))
                                    (eq.rec
                                       (eq.rec (eq.refl (lst_head = lst_head ∧ lst_tail = lst_tail))
                                          (propext
                                             {mp := λ (hl : lst_tail = lst_tail), true.intro,
                                              mpr := λ (hr : true), eq.refl lst_tail}))
                                       (eq.rec (eq.refl (and (lst_head = lst_head)))
                                          (propext
                                             {mp := λ (hl : lst_head = lst_head), true.intro,
                                              mpr := λ (hr : true), eq.refl lst_head}))))
                                 (propext {mp := and.left true, mpr := λ (h : true), ⟨h, h⟩}))))
                      (rev lst2))))
             (propext {mp := λ (hl : rev lst2 = rev lst2), true.intro, mpr := λ (hr : true), eq.refl (rev lst2)}))))
    (λ (lst1_head : mynat) (lst1_tail : mylist mynat) (lst1_ih : rev (lst1_tail ++ lst2) = rev lst2 ++ rev lst1_tail),
       eq.rec
         (eq.rec (eq.refl (rev lst2 ++ (rev lst1_tail ++ lst1_head :: empty)))
            (eq.rec
               (eq.refl
                  (rev lst2 ++ rev lst1_tail ++ lst1_head :: empty = rev lst2 ++ (rev lst1_tail ++ lst1_head :: empty)))
               (eq.rec
                  (eq.refl
                     (rev lst2 ++ rev lst1_tail ++ lst1_head :: empty =
                        rev lst2 ++ (rev lst1_tail ++ lst1_head :: empty)))
                  (mylist.rec
                     (eq.rec true.intro
                        (eq.rec (eq.refl (rev lst1_tail ++ lst1_head :: empty = rev lst1_tail ++ lst1_head :: empty))
                           (eq.rec (eq.refl (rev lst1_tail ++ lst1_head :: empty = rev lst1_tail ++ lst1_head :: empty))
                              (propext
                                 {mp := λ
                                        (hl :
                                          rev lst1_tail ++ lst1_head :: empty = rev lst1_tail ++ lst1_head :: empty),
                                          true.intro,
                                  mpr := λ (hr : true), eq.refl (rev lst1_tail ++ lst1_head :: empty)}))))
                     (λ (lst1_head_1 : mynat) (lst1_tail_1 : mylist mynat)
                      (lst1_ih :
                        lst1_tail_1 ++ rev lst1_tail ++ lst1_head :: empty =
                          lst1_tail_1 ++ (rev lst1_tail ++ lst1_head :: empty)),
                        eq.rec true.intro
                          (eq.rec
                             (eq.refl
                                (lst1_head_1 :: (lst1_tail_1 ++ rev lst1_tail ++ lst1_head :: empty) =
                                   lst1_head_1 :: (lst1_tail_1 ++ (rev lst1_tail ++ lst1_head :: empty))))
                             (eq.rec
                                (eq.rec
                                   (eq.rec
                                      (eq.rec
                                         (eq.refl
                                            (lst1_head_1 :: (lst1_tail_1 ++ rev lst1_tail ++ lst1_head :: empty) =
                                               lst1_head_1 :: (lst1_tail_1 ++ (rev lst1_tail ++ lst1_head :: empty))))
                                         (eq.rec
                                            (eq.refl
                                               (eq
                                                  (lst1_head_1 ::
                                                     (lst1_tail_1 ++ rev lst1_tail ++ lst1_head :: empty))))
                                            (eq.rec
                                               (eq.refl
                                                  (lst1_head_1 :: (lst1_tail_1 ++ rev lst1_tail ++ lst1_head :: empty)))
                                               (eq.rec
                                                  (eq.refl
                                                     (lst1_head_1 ::
                                                        (lst1_tail_1 ++ rev lst1_tail ++ lst1_head :: empty)))
                                                  lst1_ih))))
                                      (propext
                                         {mp := λ
                                                (h :
                                                  lst1_head_1 ::
                                                      (lst1_tail_1 ++ (rev lst1_tail ++ lst1_head :: empty)) =
                                                    lst1_head_1 ::
                                                      (lst1_tail_1 ++ (rev lst1_tail ++ lst1_head :: empty))),
                                                  ⟨eq.refl lst1_head_1,
                                                   eq.refl (lst1_tail_1 ++ (rev lst1_tail ++ lst1_head :: empty))⟩,
                                          mpr := λ
                                                 (a :
                                                   lst1_head_1 = lst1_head_1 ∧
                                                     lst1_tail_1 ++ (rev lst1_tail ++ lst1_head :: empty) =
                                                       lst1_tail_1 ++ (rev lst1_tail ++ lst1_head :: empty)),
                                                   and.rec
                                                     (λ (left : lst1_head_1 = lst1_head_1)
                                                      (right :
                                                        lst1_tail_1 ++ (rev lst1_tail ++ lst1_head :: empty) =
                                                          lst1_tail_1 ++ (rev lst1_tail ++ lst1_head :: empty))
                                                      («_» :
                                                        lst1_head_1 = lst1_head_1 ∧
                                                          lst1_tail_1 ++ (rev lst1_tail ++ lst1_head :: empty) =
                                                            lst1_tail_1 ++ (rev lst1_tail ++ lst1_head :: empty)),
                                                        eq.refl
                                                          (lst1_head_1 ::
                                                             (lst1_tail_1 ++ (rev lst1_tail ++ lst1_head :: empty))))
                                                     a
                                                     a}))
                                   (eq.rec
                                      (eq.rec
                                         (eq.refl
                                            (lst1_head_1 = lst1_head_1 ∧
                                               lst1_tail_1 ++ (rev lst1_tail ++ lst1_head :: empty) =
                                                 lst1_tail_1 ++ (rev lst1_tail ++ lst1_head :: empty)))
                                         (propext
                                            {mp := λ
                                                   (hl :
                                                     lst1_tail_1 ++ (rev lst1_tail ++ lst1_head :: empty) =
                                                       lst1_tail_1 ++ (rev lst1_tail ++ lst1_head :: empty)),
                                                     true.intro,
                                             mpr := λ (hr : true),
                                                      eq.refl (lst1_tail_1 ++ (rev lst1_tail ++ lst1_head :: empty))}))
                                      (eq.rec (eq.refl (and (lst1_head_1 = lst1_head_1)))
                                         (propext
                                            {mp := λ (hl : lst1_head_1 = lst1_head_1), true.intro,
                                             mpr := λ (hr : true), eq.refl lst1_head_1}))))
                                (propext {mp := and.left true, mpr := λ (h : true), ⟨h, h⟩}))))
                     (rev lst2)))))
         (eq.rec
            (eq.refl
               (rev (lst1_tail ++ lst2) ++ lst1_head :: empty = rev lst2 ++ (rev lst1_tail ++ lst1_head :: empty)))
            (eq.rec
               (eq.refl
                  (rev (lst1_tail ++ lst2) ++ lst1_head :: empty = rev lst2 ++ (rev lst1_tail ++ lst1_head :: empty)))
               lst1_ih)))
    lst1
