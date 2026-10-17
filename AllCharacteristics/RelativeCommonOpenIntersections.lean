import AllCharacteristics.RelativeCommonOpenMembership

/-!
# Intersections of common-open tuple charts

Common-open charts are exactly the finite intersections of coordinate
preimages. The construction preserves inclusions, binary intersections,
and the full open, giving the exact overlap opens used for quotient gluing.
-/

open AlgebraicGeometry CategoryTheory TopologicalSpace
namespace AllCharacteristics
universe u
variable {X S : Scheme.{u}} (f : X ⟶ S) (n : ℕ)

/-- The actual common-open tuple chart is the intersection of its coordinate preimages. -/
theorem orderedFamilyCommonOpen_eq_iInf (U : X.Opens) :
    orderedFamilyCommonOpen f U n =
      ⨅ i : Fin n, (Over.Hom.left (orderedFamilyCoordinate f n i)) ⁻¹ᵁ U := by
  apply le_antisymm
  · apply le_iInf
    intro i x hx
    exact (mem_orderedFamilyCommonOpen_iff f U n x).mp hx i
  · intro x hx
    apply (mem_orderedFamilyCommonOpen_iff f U n x).mpr
    intro i
    exact (iInf_le (fun j : Fin n ↦
      (Over.Hom.left (orderedFamilyCoordinate f n j)) ⁻¹ᵁ U) i) hx

/-- Inclusion of original opens gives inclusion of the actual common-open charts. -/
theorem orderedFamilyCommonOpen_mono {U V : X.Opens} (h : U ≤ V) :
    orderedFamilyCommonOpen f U n ≤ orderedFamilyCommonOpen f V n := by
  intro x hx
  apply (mem_orderedFamilyCommonOpen_iff f V n x).mpr
  intro i
  exact h ((mem_orderedFamilyCommonOpen_iff f U n x).mp hx i)

/-- Actual common-open chart intersections are the charts of the original intersections. -/
theorem orderedFamilyCommonOpen_inf (U V : X.Opens) :
    orderedFamilyCommonOpen f (U ⊓ V) n =
      orderedFamilyCommonOpen f U n ⊓ orderedFamilyCommonOpen f V n := by
  apply le_antisymm
  · intro x hx
    have h := (mem_orderedFamilyCommonOpen_iff f (U ⊓ V) n x).mp hx
    exact ⟨(mem_orderedFamilyCommonOpen_iff f U n x).mpr (fun i ↦ (h i).1),
      (mem_orderedFamilyCommonOpen_iff f V n x).mpr (fun i ↦ (h i).2)⟩
  · intro x hx
    apply (mem_orderedFamilyCommonOpen_iff f (U ⊓ V) n x).mpr
    intro i
    exact ⟨(mem_orderedFamilyCommonOpen_iff f U n x).mp hx.1 i,
      (mem_orderedFamilyCommonOpen_iff f V n x).mp hx.2 i⟩

/-- The common-open chart of the entire family is the entire ordered power. -/
theorem orderedFamilyCommonOpen_top :
    orderedFamilyCommonOpen f (⊤ : X.Opens) n = ⊤ := by
  apply top_unique
  intro x _
  apply (mem_orderedFamilyCommonOpen_iff f ⊤ n x).mpr
  intro i
  trivial

end AllCharacteristics
