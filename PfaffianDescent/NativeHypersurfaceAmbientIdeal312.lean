import PfaffianDescent.NativeHypersurfaceFamily297
import PfaffianDescent.NativeWholeIdealComparisonDescent300
import PfaffianDescent.NativePolynomialScalarScheme300

noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory
universe u

lemma nativeSpecRingId312 (A : Type u) [CommRing A] :
    Spec.map (CommRingCat.ofHom (RingHom.id A)) = 𝟙 (Spec (.of A)) := by
  change Spec.map (𝟙 (CommRingCat.of A)) = _
  simp only [Spec.map_id]

lemma nativePolynomialSpecId312 (R A : Type u) [CommRing R] [CommRing A]
    [Algebra R A] (m : ℕ) :
    Spec.map (CommRingCat.ofHom (MvPolynomial.map (σ := Fin m) (AlgHom.id R A).toRingHom)) =
      𝟙 (Spec (.of (MvPolynomial (Fin m) A))) := by
  have h : MvPolynomial.map (σ := Fin m) (AlgHom.id R A).toRingHom =
      RingHom.id (MvPolynomial (Fin m) A) := RingHom.ext MvPolynomial.map_id
  rw [h]
  exact nativeSpecRingId312 _

/-- Native scalar pullback of the original p=0 kernel is the exact scalar
polynomial hypersurface kernel, retaining all nilpotents. -/
lemma nativePolynomialHypersurfaceKernel_comap312
    (R A : Type u) [CommRing R] [CommRing A] [Algebra R A] (m : ℕ)
    (p : MvPolynomial (Fin m) R) :
    (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {p})))).ker.comap
        (nativePolynomialScalarMap300 R A m) =
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk
        (Ideal.span {MvPolynomial.map (algebraMap R A) p})))).ker := by
  apply nativePolynomialIdealImageKernel_comap300 (algebraMap R A)
  rw [Ideal.map_span, Set.image_singleton]

/-- The genuine297 family inside p=0 recovers the exact entire289 ambient ideal. -/
lemma affineHypersurfaceWholeQuotientHilbertPoint_ambientIdeal312
    {A : Type u} [CommRing A] {m n : ℕ}
    (I : Ideal (MvPolynomial (Fin m) A))
    (b : Module.Basis (Fin n) A (MvPolynomial (Fin m) A ⧸ I))
    (p : MvPolynomial (Fin m) A) (hp : p ∈ I) :
    (affineHypersurfaceWholeQuotientHilbertPoint297 I b p hp).val.map
        (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {p})))) =
      (affineWholeQuotientHilbertPoint289 I b).val := by
  rw [affineHypersurfaceWholeQuotientHilbertPoint_ideal297,
    Scheme.IdealSheafData.map_ker]
  change (Spec.map (CommRingCat.ofHom
      (Ideal.Quotient.factor ((Ideal.span_singleton_le_iff_mem I).mpr hp))) ≫
    Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {p})))).ker =
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))).ker
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, Ideal.Quotient.factor_comp_mk]

end PfaffianDescent
end
