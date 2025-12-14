import Lean
import Lean4Less.Commands
import Lean4Less.Ext
open Lean Lean4Less

/- Theorems for patching iota reduction -/

theorem nat_iota_zero {motive : Nat → Sort u} (zero : motive Nat.zero)
  (succ : (n : Nat) → (ih : motive n) → motive (n.succ)) :
  Nat.rec (motive := motive) zero succ 0 ≍ zero := by rfl

theorem nat_iota_succ {motive : Nat → Sort u} (zero : motive Nat.zero)
  (succ : (n : Nat) → (ih : motive n) → motive n.succ) (t : Nat) :
  Nat.rec (motive := motive) zero succ t.succ ≍
  succ t (Nat.rec (motive := motive) zero succ t) := by rfl

/- Set up the information for using those iota reduction theorem -/

def natIotaReductionData : IotaReductionData :=
  (∅ : Std.HashMap Name Name)
    |>.insert ``Nat.succ ``nat_iota_succ
    |>.insert ``Nat.zero ``nat_iota_zero

def iotaReduction : Std.HashMap Name IotaReductionData :=
  (∅ : Std.HashMap Name IotaReductionData)
  |>.insert ``Nat.rec natIotaReductionData

/- Test patching iota reduction-/
def motive := fun (_ : Nat) => Type
def zero := Unit
def succ (n : Nat) (_ : motive n) := Unit

theorem test2 (f : Unit → False) (t : Nat.rec (motive := motive) zero succ 1) :
  False := f t
theorem test3 (f : Unit → False) (t : Nat.rec (motive := motive) zero succ 0) :
  False := f t

/--
info: fun f t => f (L4L.castHEq (nat_iota_succ zero succ 0) t)
-/
#guard_msgs in
#patch_const test2 (iotaReduction := iotaReduction) -kLikeReduction -proofIrrelevance

/--
info: fun f t => f (L4L.castHEq (nat_iota_zero zero succ) t)
-/
#guard_msgs in
#patch_const test3 (iotaReduction := iotaReduction) -kLikeReduction -proofIrrelevance

/--
info: fun x x_1 x_2 =>
  Nat.brecOn (motive := fun x => ∀ (x_3 : Nat), x ≤ x_3 → x = x_3 ∨ x < x_3) x
    (fun x f x_3 x_4 =>
      (match (motive :=
          ∀ (x x_5 : Nat),
            x ≤ x_5 →
              ∀ (x_7 : Nat.below (motive := fun x => ∀ (x_7 : Nat), x ≤ x_7 → x = x_7 ∨ x < x_7) x), x = x_5 ∨ x < x_5)
          x, x_3, x_4 with
        | Nat.zero, Nat.zero, x => fun x => Or.inl rfl
        | Nat.zero, n.succ, x => fun x => Or.inr (Nat.succ_le_succ (Nat.zero_le n))
        | n.succ, Nat.zero, h => fun x => absurd h (Nat.not_succ_le_zero n)
        | n.succ, m.succ, h => fun x =>
          let this := Nat.le_of_succ_le_succ h;
          match x.1 m this with
          | Or.inl h => Or.inl (h ▸ rfl)
          | Or.inr h =>
            Or.inr
              (L4L.castHEq
                (L4L.appArgHEq' (fun n => n.le m.succ)
                  (L4L.appArgHEq Nat.succ
                    (L4L.appArgHEq Nat.succ
                      (HEq.trans
                        (L4L.appArgHEq' (fun f => f n)
                          (L4L.appHEqABUV'
                            (L4L.appArgHEq' (PProd ((fun x => Nat → Nat) 0))
                              (nat_iota_zero PUnit fun n n_ih => (fun x => Nat → Nat) n ×' n_ih))
                            (fun a a_1 a_2 =>
                              L4L.HEqRefl
                                ((fun β a => (fun x => Nat → Nat) 0) (Nat.below (motive := fun x => Nat → Nat) 0) a))
                            (L4L.appArgHEq' ((fun α β a => a.1) ((fun x => Nat → Nat) 0))
                              (nat_iota_zero PUnit fun n n_ih => (fun x => Nat → Nat) n ×' n_ih))
                            (nat_iota_zero
                              ⟨(fun x f x_5 =>
                                    (match (motive :=
                                        Nat → (x : Nat) → Nat.below (motive := fun x => Nat → Nat) x → Nat) x_5, x with
                                      | a, Nat.zero => fun x => a
                                      | a, b.succ => fun x => (x.1 a).succ)
                                      f)
                                  Nat.zero PUnit.unit,
                                PUnit.unit⟩
                              fun n n_ih =>
                              ⟨(fun x f x_5 =>
                                    (match (motive :=
                                        Nat → (x : Nat) → Nat.below (motive := fun x => Nat → Nat) x → Nat) x_5, x with
                                      | a, Nat.zero => fun x => a
                                      | a, b.succ => fun x => (x.1 a).succ)
                                      f)
                                  n.succ n_ih,
                                n_ih⟩)))
                        (nat_iota_zero ((fun a x => a) n) fun n_1 n_ih =>
                          (fun n_2 => (fun a b x => (x.1 a).succ) n n_2) n_1)))))
                (Nat.succ_le_succ
                  (L4L.castHEq
                    (L4L.appArgHEq' (fun n => n.le m)
                      (HEq.trans
                        (L4L.appArgHEq Nat.succ
                          (HEq.trans
                            (nat_iota_zero ((fun a x => a) n) fun n_1 n_ih =>
                              (fun n_2 => (fun a b x => (x.1 a).succ) n n_2) n_1)
                            (L4L.appArgHEq' (fun f => f n)
                              (HEq.symm
                                (L4L.appHEqABUV'
                                  (L4L.appArgHEq' (PProd ((fun x => Nat → Nat) 0))
                                    (nat_iota_zero PUnit fun n n_ih => (fun x => Nat → Nat) n ×' n_ih))
                                  (fun a a_1 a_2 =>
                                    L4L.HEqRefl
                                      ((fun β a => (fun x => Nat → Nat) 0) (Nat.below (motive := fun x => Nat → Nat) 0)
                                        a))
                                  (L4L.appArgHEq' ((fun α β a => a.1) ((fun x => Nat → Nat) 0))
                                    (nat_iota_zero PUnit fun n n_ih => (fun x => Nat → Nat) n ×' n_ih))
                                  (nat_iota_zero
                                    ⟨(fun x f x_5 =>
                                          (match (motive :=
                                              Nat → (x : Nat) → Nat.below (motive := fun x => Nat → Nat) x → Nat) x_5,
                                              x with
                                            | a, Nat.zero => fun x => a
                                            | a, b.succ => fun x => (x.1 a).succ)
                                            f)
                                        Nat.zero PUnit.unit,
                                      PUnit.unit⟩
                                    fun n n_ih =>
                                    ⟨(fun x f x_5 =>
                                          (match (motive :=
                                              Nat → (x : Nat) → Nat.below (motive := fun x => Nat → Nat) x → Nat) x_5,
                                              x with
                                            | a, Nat.zero => fun x => a
                                            | a, b.succ => fun x => (x.1 a).succ)
                                            f)
                                        n.succ n_ih,
                                      n_ih⟩))))))
                        (L4L.appArgHEq' (fun f => f n)
                          (HEq.symm
                            (L4L.appHEqABUV'
                              (L4L.appArgHEq' (PProd ((fun x => Nat → Nat) 1))
                                (HEq.trans (nat_iota_succ PUnit (fun n n_ih => (fun x => Nat → Nat) n ×' n_ih) 0)
                                  (L4L.appArgHEq' (PProd ((fun x => Nat → Nat) 0))
                                    (HEq.trans (nat_iota_zero PUnit fun n n_ih => (fun x => Nat → Nat) n ×' n_ih)
                                      (nat_iota_zero PUnit fun n n_ih => (fun x => Nat → Nat) n ×' n_ih)))))
                              (fun a a_1 a_2 =>
                                L4L.HEqRefl
                                  ((fun β a => (fun x => Nat → Nat) 1) (Nat.below (motive := fun x => Nat → Nat) 1) a))
                              (L4L.appArgHEq' ((fun α β a => a.1) ((fun x => Nat → Nat) 1))
                                (HEq.trans (nat_iota_succ PUnit (fun n n_ih => (fun x => Nat → Nat) n ×' n_ih) 0)
                                  (L4L.appArgHEq' (PProd ((fun x => Nat → Nat) 0))
                                    (HEq.trans (nat_iota_zero PUnit fun n n_ih => (fun x => Nat → Nat) n ×' n_ih)
                                      (nat_iota_zero PUnit fun n n_ih => (fun x => Nat → Nat) n ×' n_ih)))))
                              (nat_iota_succ
                                ⟨(fun x f x_5 =>
                                      (match (motive :=
                                          Nat → (x : Nat) → Nat.below (motive := fun x => Nat → Nat) x → Nat) x_5,
                                          x with
                                        | a, Nat.zero => fun x => a
                                        | a, b.succ => fun x => (x.1 a).succ)
                                        f)
                                    Nat.zero PUnit.unit,
                                  PUnit.unit⟩
                                (fun n n_ih =>
                                  ⟨(fun x f x_5 =>
                                        (match (motive :=
                                            Nat → (x : Nat) → Nat.below (motive := fun x => Nat → Nat) x → Nat) x_5,
                                            x with
                                          | a, Nat.zero => fun x => a
                                          | a, b.succ => fun x => (x.1 a).succ)
                                          f)
                                      n.succ n_ih,
                                    n_ih⟩)
                                0))))))
                    h))))
        f)
    x_1 x_2
-/
#guard_msgs in
#patch_const Nat.eq_or_lt_of_le (iotaReduction := iotaReduction) -kLikeReduction -proofIrrelevance
