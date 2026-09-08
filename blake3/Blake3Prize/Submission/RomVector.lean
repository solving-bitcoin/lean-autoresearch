import Blake3Prize.Submission.RomBytes

namespace Blake3Prize.Submission.RomVector

def cons (head : α) (tail : Vector α n) : Vector α (n+1) :=
  Vector.ofFn (Fin.cases head tail.get)

@[simp] theorem get_cons_zero (head : α) (tail : Vector α n) :
    (cons head tail).get 0 = head := by simp [cons]

@[simp] theorem get_cons_succ (head : α) (tail : Vector α n) (i : Fin n) :
    (cons head tail).get i.succ = tail.get i := by simp [cons]

def drop (values : Vector α (n+1)) : Vector α n :=
  Vector.ofFn fun i => values.get i.succ

@[simp] theorem get_drop (values : Vector α (n+1)) (i : Fin n) :
    (drop values).get i = values.get i.succ := by simp [drop]

theorem cons_drop (values : Vector α (n+1)) : cons (values.get 0) (drop values) = values := by
  apply Vector.ext
  intro i hi
  exact Fin.cases
    (motive := fun j : Fin (n+1) =>
      (cons (values.get 0) (drop values)).get j = values.get j)
    (by simp) (fun j => by simp) (⟨i,hi⟩ : Fin (n+1))

@[simp] theorem map_cons (f : α → β) (head : α) (tail : Vector α n) :
    (cons head tail).map f = cons (f head) (tail.map f) := by
  apply Vector.ext
  intro i hi
  have h := Fin.cases
    (motive := fun j : Fin (n+1) => ((cons head tail).map f).get j =
      (cons (f head) (tail.map f)).get j)
    (by simp) (fun j => by simp) (⟨i,hi⟩ : Fin (n+1))
  exact h

@[simp] theorem drop_map (f : α → β) (values : Vector α (n+1)) :
    drop (values.map f) = (drop values).map f := by
  ext i hi
  simp [drop,Vector.get_eq_getElem]

theorem append_get_left (left : Vector α n) (right : Vector α m) (i : Fin n) :
    (left ++ right).get ⟨i.val,by omega⟩ = left.get i :=
  Vector.getElem_append_left i.isLt

theorem append_get_right (left : Vector α n) (right : Vector α m) (i : Fin m) :
    (left ++ right).get ⟨n+i.val,by omega⟩ = right.get i := by
  simpa only [Vector.get_eq_getElem,Nat.add_sub_cancel_left] using
    (Vector.getElem_append_right (xs := left) (ys := right)
      (i := n+i.val) (by omega) (by omega))

end Blake3Prize.Submission.RomVector
