import PfaffianDescent.WholeClosedAffineQuotient180
import PfaffianDescent.NilpotentCartesianFieldPointSupport176
import PfaffianDescent.SmoothCubicOriginalFamilyStalkBridge172

/-! Source-only180. Preserve the SAME whole old Z in an ACTUAL canonical
tensor chart. Original Artin field-point geometry supplies support containment;
the actual quotient and its finite-flat properties are conclusions. -/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped TensorProduct
universe u

/-- The whole original old deformation is the quotient by its ACTUAL
coordinate ideal in the canonical tensor chart. The old finite-flat map and
all original scalar coefficients are preserved. No support, quotient,
quotient-flatness, quotient-finiteness or regularity certificate is supplied. -/
lemma exists_wholeOldTensorQuotient180
    {R S A' K L : Type u} [CommRing R] [CommRing S] [CommRing A']
    [Algebra R S] [Algebra R A'] [IsArtinianRing S] [IsLocalRing S]
    [Field K] [Field L] {X X0 Z : Scheme.{u}}
    (F : X ⟶ Spec (.of S)) (b : S →+* K) (hb : Function.Surjective b)
    (d : X0 ⟶ X) (F0 : X0 ⟶ Spec (.of K))
    (H0 : IsPullback d F0 F (Spec.map (CommRingCat.ofHom b)))
    (i : Z ⟶ X) [IsClosedImmersion i] [IsFinite (i ≫ F)] [Flat (i ≫ F)]
    (u0 : Spec (.of L) ⟶ Z) (v : Spec (.of L) ⟶ X0)
    (H : IsPullback u0 v i d)
    (a : Spec (.of (S ⊗[R] A')) ⟶ X) [IsOpenImmersion a]
    (ha : a ≫ F = Spec.map (CommRingCat.ofHom (algebraMap S (S ⊗[R] A'))))
    (hpoint : d (v default) ∈ Set.range a) :
    ∃ (j : Z ⟶ Spec (.of (S ⊗[R] A'))) (hj : IsClosedImmersion j),
      j ≫ a = i ∧
      letI := hj
      let T := S ⊗[R] A'
      let J := closedAffineCoordinateIdeal180 j
      let V : X.affineOpens :=
        ⟨a ''ᵁ ⊤, (isAffineOpen_top (Spec (.of T))).image_of_isOpenImmersion a⟩
      let Echart := (a.appIso ⊤ ≪≫ Scheme.ΓSpecIso (.of T)).commRingCatIsoToRingEquiv
      J = (i.ker.ideal V).map Echart.toRingHom ∧
      (closedAffineSectionMap180 j).comp (algebraMap S T) =
        closedAffineSectionMap180 (i ≫ F) ∧
      (∀ t : T, closedAffineQuotientRingEquiv180 j (Ideal.Quotient.mk J t) =
        closedAffineSectionMap180 j t) ∧
      (∀ s : S, closedAffineQuotientRingEquiv180 j (algebraMap S (T ⧸ J) s) =
        closedAffineSectionMap180 (i ≫ F) s) ∧
      (closedAffineQuotientIso180 j).hom ≫
        Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)) ≫ a = i ∧
      (closedAffineQuotientIso180 j).hom ≫
        Spec.map (CommRingCat.ofHom (algebraMap S (T ⧸ J))) = i ≫ F ∧
      IsFinite (Spec.map (CommRingCat.ofHom (algebraMap S (T ⧸ J)))) ∧
      Flat (Spec.map (CommRingCat.ofHom (algebraMap S (T ⧸ J)))) := by
  let T := S ⊗[R] A'
  have hnil := smoothCubic_artin_residueKernel_isNilpotent172 b hb
  have hsupport := nilpotentCartesianFieldPoint_support176
    F b hb hnil d F0 H0 i u0 v H
  have hrange : Set.range i ⊆ Set.range a := by
    rintro _ ⟨z, rfl⟩
    rw [hsupport z]
    exact hpoint
  let j : Z ⟶ Spec (.of T) := IsOpenImmersion.lift a i hrange
  have hfac : j ≫ a = i := IsOpenImmersion.lift_fac a i hrange
  letI : IsClosedImmersion (j ≫ a) := by rw [hfac]; infer_instance
  letI : IsClosedImmersion j := IsClosedImmersion.of_comp j a
  have hbase : j ≫ Spec.map (CommRingCat.ofHom (algebraMap S T)) = i ≫ F := by
    calc
      _ = j ≫ (a ≫ F) := by rw [ha]
      _ = _ := by rw [← Category.assoc, hfac]
  letI : IsFinite (j ≫ Spec.map (CommRingCat.ofHom (algebraMap S T))) := by
    rw [hbase]
    infer_instance
  letI : Flat (j ≫ Spec.map (CommRingCat.ofHom (algebraMap S T))) := by
    rw [hbase]
    infer_instance
  let J := closedAffineCoordinateIdeal180 j
  have hcoef : (closedAffineSectionMap180 j).comp (algebraMap S T) =
      closedAffineSectionMap180 (i ≫ F) := by
    rw [closedAffineSectionMap180_comp_scalar, hbase]
  have hscalar : ∀ s : S,
      closedAffineQuotientRingEquiv180 j (algebraMap S (T ⧸ J) s) =
        closedAffineSectionMap180 (i ≫ F) s := by
    intro s
    change closedAffineQuotientRingEquiv180 j
      (Ideal.Quotient.mk J (algebraMap S T s)) = _
    rw [closedAffineQuotientRingEquiv180_mk]
    exact DFunLike.congr_fun hcoef s
  obtain ⟨hqbase, hqfinite, hqflat⟩ := closedAffineQuotient180_finite_flat (S := S) j
  refine ⟨j, inferInstance, hfac,
    closedAffineCoordinateIdeal180_eq_chart_ideal i a j hfac,
    hcoef, closedAffineQuotientRingEquiv180_mk j, hscalar, ?_,
    hqbase.trans hbase, hqfinite, hqflat⟩
  rw [← Category.assoc, closedAffineQuotientIso180_fac, hfac]

end PfaffianDescent
