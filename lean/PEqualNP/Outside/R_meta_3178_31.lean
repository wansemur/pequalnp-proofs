import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

set_option maxHeartbeats 1000000 in
theorem PEqualNP.Outside.R_meta_3178_31
    (transport : ∀ (n : ℕ) (p : ℕ → ℕ), (∀ i < n, p i < n) → (∀ i, n ≤ i → p i = i) →
      ∀ C : Circuit, FanInTwo C → ∃ D : Circuit, FanInTwo D ∧ D.size = C.size ∧
        ∀ u v : List Bool, u.length = n → v.length = n →
          (∀ i, u.getD (p i) false = v.getD i false) → D.eval u = C.eval v)
    (search : ∀ j : Fin 9, (j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 6) → ∀ C : Circuit, FanInTwo C → C.size ≤ 13 →
      ∃ x : Fin 9 → Bool, C.eval (List.ofFn x ++ [!x 0, x 0 || x j]) ≠ ((x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5))) :
    ∀ (x1 : List ℕ),   x1.length = (2 : ℕ) →     (∀ x3 ∈ x1, x3 < (10 : ℕ)) →       (0 : ℕ) ∈ x1 ∨ (9 : ℕ) ∈ x1 →         (¬∀ x5 ∈ x1, x5 = (0 : ℕ) ∨ x5 = (9 : ℕ)) ∧ (0 : ℕ) ∈ x1 →           ∀ (x6 : PEqualNP.CircuitLowerBounds.Circuit),             PEqualNP.MetaComplexity.FanInTwo x6 →               x6.size ≤ (13 : ℕ) →                 ∃ (x9 : Fin (9 : ℕ) → Bool),                   have x10 : List Bool := List.ofFn x9 ++ [!x9 (0 : Fin (9 : ℕ))];                   x6.eval (x10 ++ [PEqualNP.CircuitLowerBounds.GateOp.or.eval (List.map (fun (x11 : ℕ) => x10.getD x11 Bool.false) x1)]) ≠ (x9 (0 : Fin (9 : ℕ)) && x9 (1 : Fin (9 : ℕ)) || x9 (1 : Fin (9 : ℕ)) && x9 (2 : Fin (9 : ℕ)) || x9 (2 : Fin (9 : ℕ)) && x9 (3 : Fin (9 : ℕ)) || x9 (3 : Fin (9 : ℕ)) && x9 (4 : Fin (9 : ℕ)) || x9 (4 : Fin (9 : ℕ)) && x9 (0 : Fin (9 : ℕ)) || x9 (0 : Fin (9 : ℕ)) && x9 (5 : Fin (9 : ℕ)) || x9 (1 : Fin (9 : ℕ)) && x9 (6 : Fin (9 : ℕ)) || x9 (2 : Fin (9 : ℕ)) && x9 (7 : Fin (9 : ℕ)) || x9 (3 : Fin (9 : ℕ)) && x9 (8 : Fin (9 : ℕ)) || x9 (5 : Fin (9 : ℕ)) && x9 (7 : Fin (9 : ℕ)) || x9 (6 : Fin (9 : ℕ)) && x9 (8 : Fin (9 : ℕ)) || x9 (8 : Fin (9 : ℕ)) && x9 (5 : Fin (9 : ℕ))) := by
  let row (j : Fin 9) (x : Fin 9 → Bool) := List.ofFn x ++ [!x 0, x 0 || x j]
  let edge (x : Fin 9 → Bool) := (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)
  let rep (j : Fin 9) := j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 6
  let σ : Fin 9 → Fin 9 := ![0,5,8,3,4,1,7,6,2]
  let p (i : ℕ) := if h : i < 9 then (σ ⟨i,h⟩).val else i
  have small : ∀ i < 11, p i < 11 := by
    intro i hi
    dsimp [p]
    split <;> omega
  have large : ∀ i, 11 ≤ i → p i = i := by
    intro i hi
    simp [p, show ¬ i < 9 by omega]
  have symmEdge (x : Fin 9 → Bool) : edge (x ∘ σ) = edge x := by
    change ((x 0 && x 5) || (x 5 && x 8) || (x 8 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 1) || (x 5 && x 7) || (x 8 && x 6) || (x 3 && x 2) || (x 1 && x 6) || (x 7 && x 2) || (x 2 && x 1)) = ((x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5))
    ac_rfl
  have symmRows (j : Fin 9) (x : Fin 9 → Bool) (i : ℕ) :
      (row (σ j) x).getD (p i) false = (row j (x ∘ σ)).getD i false := by
    by_cases hi : i < 11
    · interval_cases i <;> rfl
    · rw [large i (by omega), List.getD_eq_default _ _ (by simp [row]; omega),
        List.getD_eq_default _ _ (by simp [row]; omega)]
  intro pins hlen hbound _ hmix C hfan hsize
  obtain ⟨a,b,hpins⟩ : ∃ a b, pins = [a,b] := by
    cases pins with
    | nil => simp at hlen
    | cons a tail =>
      cases tail with
      | nil => simp at hlen
      | cons b tail =>
        cases tail with
        | nil => exact ⟨_,_,rfl⟩
        | cons => simp at hlen
  subst pins
  have hab : a = 0 ∨ b = 0 := by simpa [eq_comm] using hmix.2
  have nonspecial : ¬ ((a = 0 ∨ a = 9) ∧ (b = 0 ∨ b = 9)) := by simpa using hmix.1
  have ab := hbound a (by simp)
  have bb := hbound b (by simp)
  obtain ⟨j,hj,hrow⟩ : ∃ j : Fin 9, j ≠ 0 ∧ ∀ x : Fin 9 → Bool,
      let w := List.ofFn x ++ [!x 0]
      w ++ [GateOp.or.eval ([a,b].map fun i => w.getD i false)] = row j x := by
    rcases hab with rfl | rfl
    · have hb : b ≠ 0 ∧ b ≠ 9 := by tauto
      refine ⟨⟨b,by omega⟩, fun h => hb.1 (congrArg Fin.val h), ?_⟩
      intro x
      have blt : b < 9 := by omega
      interval_cases b <;> simp [row,GateOp.eval]
    · have ha : a ≠ 0 ∧ a ≠ 9 := by tauto
      refine ⟨⟨a,by omega⟩, fun h => ha.1 (congrArg Fin.val h), ?_⟩
      intro x
      have alt : a < 9 := by omega
      interval_cases a <;> simp [row,GateOp.eval] <;> exact Bool.or_comm _ _
  change ∃ x : Fin 9 → Bool, C.eval _ ≠ edge x
  have enough : ∃ x, C.eval (row j x) ≠ edge x := by
    by_cases hr : rep j
    · exact search j hr C hfan hsize
    · have hs : rep (σ j) := by
        fin_cases j <;> first | exact False.elim (hj rfl) | exact False.elim (hr (by decide)) | decide
      obtain ⟨D,hD,hcount,hDval⟩ := transport 11 p small large C hfan
      obtain ⟨x,hx⟩ := search (σ j) hs D hD (hcount ▸ hsize)
      refine ⟨x ∘ σ, fun eq => hx ?_⟩
      rw [hDval _ _ (by simp [row]) (by simp [row]) (symmRows j x),eq,symmEdge]
  obtain ⟨x,hx⟩ := enough
  exact ⟨x, by simpa only [hrow x] using hx⟩
