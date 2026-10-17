import AllCharacteristics.RelativeCommonOpenQuotientGluing

/-!
# Exact chart intersections in the glued unordered-tuple quotient

Two points in glued quotient charts agree precisely when they come from
the quotient of the actual common-open intersection.
-/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
namespace AllCharacteristics
universe u
variable {X S : Scheme.{u}} (f : X ⟶ S) [IsAffine S] (n : ℕ) [hSep : X.IsSeparated]

/-- The original affine intersection chart gives exactly the point identifications
between two charts in the actual glued quotient scheme. -/
theorem commonOpenTupleQuotientGluedChart_eq_iff (U V : X.affineOpens)
    (x : commonOpenTupleQuotient f U.val n) (y : commonOpenTupleQuotient f V.val n) :
    commonOpenTupleQuotientGluedChart f n U x = commonOpenTupleQuotientGluedChart f n V y ↔
      ∃ z : commonOpenTupleQuotient f (U.val ⊓ V.val) n,
        commonOpenTupleQuotientInclusion f (show U.val ⊓ V.val ≤ U.val from inf_le_left) n z = x ∧
        commonOpenTupleQuotientInclusion f (show U.val ⊓ V.val ≤ V.val from inf_le_right) n z = y := by
  let I : X.affineOpens := ⟨U.val ⊓ V.val, U.property.inf V.property⟩
  have hIU : I ≤ U := show U.val ⊓ V.val ≤ U.val from inf_le_left
  have hIV : I ≤ V := show U.val ⊓ V.val ≤ V.val from inf_le_right
  constructor
  · intro h
    obtain ⟨W, hWU, hWV, z, hzx, hzy⟩ :=
      (Scheme.IsLocallyDirected.ι_eq_ι_iff (commonOpenTupleQuotientDiagram f n)).mp h
    have hWI : W ≤ I := show W.val ≤ U.val ⊓ V.val from le_inf hWU.le hWV.le
    refine ⟨commonOpenTupleQuotientInclusion f hWI n z, ?_, ?_⟩
    · have he := congrArg (fun m : commonOpenTupleQuotient f W.val n ⟶
          commonOpenTupleQuotient f U.val n ↦ m z)
        (commonOpenTupleQuotientInclusion_comp f n hWI hIU W.property I.property U.property)
      exact he.trans hzx
    · have he := congrArg (fun m : commonOpenTupleQuotient f W.val n ⟶
          commonOpenTupleQuotient f V.val n ↦ m z)
        (commonOpenTupleQuotientInclusion_comp f n hWI hIV W.property I.property V.property)
      exact he.trans hzy
  · rintro ⟨z, rfl, rfl⟩
    have heU := congrArg (fun m : commonOpenTupleQuotient f I.val n ⟶
        commonOpenTupleQuotientGlued f n ↦ m z)
      (commonOpenTupleQuotientGluedChart_naturality f n (homOfLE hIU))
    have heV := congrArg (fun m : commonOpenTupleQuotient f I.val n ⟶
        commonOpenTupleQuotientGlued f n ↦ m z)
      (commonOpenTupleQuotientGluedChart_naturality f n (homOfLE hIV))
    exact heU.trans heV.symm

end AllCharacteristics
