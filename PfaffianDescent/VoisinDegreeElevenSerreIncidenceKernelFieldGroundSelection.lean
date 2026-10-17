import PfaffianDescent.VoisinDegreeElevenSerreIncidenceGroundFrameNativeOpen
import PfaffianDescent.VoisinDegreeElevenSerreIncidenceKernelFieldSeedOpen

/-! # An actual incidence seed selects a ground kernel-frame parameter -/
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MvPolynomial
open AllCharacteristics.HomogeneousProjective
namespace PfaffianDescent
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false

theorem serreIncidenceKernelField_exists_ground_selection
    {F E : Type u} [Field F] [Field E] [Algebra F E] [Infinite F]
    {B I : Scheme.{u}} (π : I ⟶ B) (c : Spec (.of E) ⟶ B)
    (A : Matrix (Fin 6) (Fin 9) E)
    (e : scheme (serreEvaluationHomogeneousIdeal A) ≅ pullback π c)
    (he : e.hom ≫ pullback.snd π c = toBase (serreEvaluationHomogeneousIdeal A))
    (M : Matrix (Fin 9) (Fin 3) F) (N : Matrix (Fin 3) (Fin 9) F)
    (hNM : N * M = 1)
    (hrange : LinearMap.range (Matrix.toLin' (M.map (algebraMap F E))) =
      LinearMap.ker (Matrix.toLin' A))
    (honto : Function.Surjective (Matrix.toLin' A))
    (W : I.Opens) (s : Spec (.of E) ⟶ I) (hs : s ≫ π = c)
    (x : Spec (.of E)) (hx : s x ∈ W) :
    let U := (e.hom ≫ pullback.fst π c) ⁻¹ᵁ W
    ∃ (qF : Spec (.of F) ⟶ scheme (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin 3) F)))
      (q : Spec (.of E) ⟶ (U : Scheme.{u})),
      qF ≫ toBase (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin 3) F)) = 𝟙 _ ∧
      (q ≫ U.ι ≫ e.hom ≫ pullback.fst π c) ≫ π = c ∧
      (∀ y : Spec (.of E), (q ≫ U.ι ≫ e.hom ≫ pullback.fst π c) y ∈ W) ∧
      q ≫ U.ι ≫ schemeQuotientMap
        (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin 9) E))
        (serreEvaluationHomogeneousIdeal A) bot_le ≫
        projectiveCoefficientMap (algebraMap F E)
          (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin 9) F))
          (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin 9) E)) (by simp) =
        Spec.map (CommRingCat.ofHom (algebraMap F E)) ≫ qF ≫
          serreKernelFrameProjectiveEmbedding M N hNM := by
  let U := (e.hom ≫ pullback.fst π c) ⁻¹ᵁ W
  have hU : (U : Set (scheme (serreEvaluationHomogeneousIdeal A))).Nonempty :=
    serreIncidenceKernelFieldOpen_nonempty_of_seed π c e W s hs x hx
  obtain ⟨qF, q, hF, hE, hcoeff⟩ :=
    serreIncidenceGroundFrameNativeOpen_exists_ground_parameter M N hNM A hrange honto U hU
  refine ⟨qF, q, hF, ?_, ?_, hcoeff⟩
  · rw [Category.assoc, Category.assoc, Category.assoc, pullback.condition,
      ← Category.assoc e.hom, he]
    simpa only [Category.assoc, Category.id_comp] using
      congrArg (fun z => z ≫ c) hE
  · intro y
    change (e.hom ≫ pullback.fst π c) (U.ι (q y)) ∈ W
    exact (q y).property

end PfaffianDescent
