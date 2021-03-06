λ {lst : mylist mynat},
  mylist.rec
    (eq.rec true.intro
       (eq.rec (eq.refl (empty = empty))
          (eq.rec (eq.refl (empty = empty))
             (propext {mp := λ (hl : empty = empty), true.intro, mpr := λ (hr : true), eq.refl empty}))))
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
                           {mp := λ (hl : lst_tail = lst_tail), true.intro, mpr := λ (hr : true), eq.refl lst_tail}))
                     (eq.rec (eq.refl (and (lst_head = lst_head)))
                        (propext
                           {mp := λ (hl : lst_head = lst_head), true.intro,
                            mpr := λ (hr : true), eq.refl lst_head}))))
               (propext {mp := and.left true, mpr := λ (h : true), ⟨h, h⟩}))))
    lst
