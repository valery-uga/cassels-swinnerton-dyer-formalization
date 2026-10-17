import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.RingTheory.Ideal.Quotient.Operations

/-! Full affine quotient base change, with no flatness/reducedness premise. -/
noncomputable section
namespace PfaffianDescent.Coray
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u
set_option autoImplicit false
variable {R S : Type u} [CommRing R] [CommRing S]

/-- The actual quotient-to-extended-quotient map induced by the SAME f. -/
def nativeQuotientBaseChangeMap (f : R →+* S) (I : Ideal R) : R ⧸ I →+* S ⧸ I.map f :=
  Ideal.Quotient.lift I ((Ideal.Quotient.mk (I.map f)).comp f) (by
    intro r hr
    apply Ideal.Quotient.eq_zero_iff_mem.mpr
    exact Ideal.mem_map_of_mem f hr)

/-- Native CommRingCat pushout comes directly from the full quotient universal
property. Flatness, radical ideals and abstract tensor identifications are
unnecessary and not assumed. -/
theorem nativeQuotientBaseChange_isPushout001 (f : R →+* S) (I : Ideal R) :
    IsPushout (CommRingCat.ofHom (Ideal.Quotient.mk I)) (CommRingCat.ofHom f)
      (CommRingCat.ofHom (nativeQuotientBaseChangeMap f I))
      (CommRingCat.ofHom (Ideal.Quotient.mk (I.map f))) := by
  apply IsPushout.mk'
  · apply CommRingCat.hom_ext
    apply RingHom.ext
    intro r
    rfl
  · intro T phi psi _hLeft hRight
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro x
    obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective x
    exact congrArg (fun g : CommRingCat.of S ⟶ T => g.hom s) hRight
  · intro T alpha beta hComm
    have hKernel : I.map f ≤ RingHom.ker beta.hom := by
      rw [Ideal.map_le_iff_le_comap]
      intro r hr
      change beta.hom (f r) = 0
      have h := congrArg (fun g : CommRingCat.of R ⟶ T => g.hom r) hComm
      change alpha.hom (Ideal.Quotient.mk I r) = beta.hom (f r) at h
      exact h.symm.trans ((congrArg alpha.hom
        (Ideal.Quotient.eq_zero_iff_mem.mpr hr)).trans (map_zero alpha.hom))
    let ell : S ⧸ I.map f →+* T :=
      Ideal.Quotient.lift (I.map f) beta.hom (fun s hs => hKernel hs)
    refine ⟨CommRingCat.ofHom ell, ?_, ?_⟩
    · apply CommRingCat.hom_ext
      apply RingHom.ext
      intro x
      obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective x
      change beta.hom (f r) = alpha.hom (Ideal.Quotient.mk I r)
      exact (congrArg (fun g : CommRingCat.of R ⟶ T => g.hom r) hComm).symm
    · apply CommRingCat.hom_ext
      apply RingHom.ext
      intro s
      rfl

/-- The literal affine quotient Spec(S/I_S) IS the full native pullback of
Spec(R/I) along Spec(f). Nilpotents and multiplicities remain intact. -/
theorem nativeQuotientBaseChange_isPullback001 (f : R →+* S) (I : Ideal R) :
    IsPullback
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I.map f))))
      (Spec.map (CommRingCat.ofHom (nativeQuotientBaseChangeMap f I)))
      (Spec.map (CommRingCat.ofHom f))
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))) :=
  (isPullback_SpecMap_of_isPushout
    (CommRingCat.ofHom (Ideal.Quotient.mk I)) (CommRingCat.ofHom f)
    (CommRingCat.ofHom (nativeQuotientBaseChangeMap f I))
    (CommRingCat.ofHom (Ideal.Quotient.mk (I.map f)))
    (nativeQuotientBaseChange_isPushout001 f I)).flip

end PfaffianDescent.Coray
