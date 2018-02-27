import .category

open categories
definition Rel : category Type := {
  Hom := λ X Y, X → Y → Prop,
  identity := λ X, λ x y, x = y,
  compose := λ X Y Z f g x z, ∃ y, f x y ∧ g y z,
  associativity := begin
                    tidy,
                    apply propext,
                    split,
                    {
                        intros,
                        cases a,
                        cases a_h,
                        cases a_h_left,
                        cases a_h_left_h,
                        existsi a_h_left_w,
                        split, 
                        { exact a_h_left_h_left }, 
                        { existsi a_w, split, exact a_h_left_h_right, exact a_h_right }
                    },
                    {
                        intros,
                        cases a,
                        cases a_h,
                        cases a_h_right,
                        cases a_h_right_h,
                        existsi a_h_right_w,
                        split, 
                        { existsi a_w, split, exact a_h_left, exact a_h_right_h_left },
                        { exact a_h_right_h_right }
                    },
                  end
}