import PfaffianDescent.VoisinDegreeElevenSerreIncidenceCanonicalRowPresentation
import PfaffianDescent.VoisinDegreeElevenSerreIncidenceIdealIsoTransport
import PfaffianDescent.VoisinDegreeElevenSerreIncidenceNativePlane

/-! # The actual rank-nine bundle incidence is the projective plane kernel family -/
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MvPolynomial
open AllCharacteristics.HomogeneousProjective
namespace PfaffianDescent
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false

theorem serreIncidence_exists_plane_of_rank_rows_minor
    {K : Type u} [CommRing K] {B : Scheme.{u}} [IsAffine B]
    (b : B ⟶ Spec (.of K)) {n : ℕ} (h9 : n = 9)
    (I : (pullback b (toBase (⊥ : HomogeneousIdeal
      (homogeneousSubmodule (Fin n) K)))).IdealSheafData)
    (A : Matrix (Fin 6) (Fin n) Γ(B, ⊤))
    (h : ∀ j : Fin n, I.comap (serreIncidenceRankProductChart b j) =
      Scheme.IdealSheafData.ofIdealTop
        (Ideal.span (Set.range (serreIncidenceRankProductRow b j A))))
    (m : Fin 6 ↪ Fin 9)
    (hm : IsUnit (Matrix.submatrix (fun r k => A r ((finCongr h9).symm k)) id m).det) :
    ∃ e : scheme (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin 3) Γ(B, ⊤))) ≅
        I.subscheme,
      e.hom ≫ I.subschemeι ≫ pullback.fst b
        (toBase (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin n) K))) =
        toBase (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin 3) Γ(B, ⊤))) ≫
          B.isoSpec.inv ∧
      IsOpenMap (I.subschemeι ≫ pullback.fst b
        (toBase (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin n) K)))) := by
  let q := serreIncidenceProductRankIso b h9
  let I' := I.comap q.inv
  let A' : Matrix (Fin 6) (Fin 9) Γ(B, ⊤) := fun r k => A r ((finCongr h9).symm k)
  have hr := serreIncidenceProductRank_equations b h9 I A h
  obtain ⟨eP, hp, hopen⟩ := serreIncidence_exists_native_plane_of_rows_minor b I' A' hr m hm
  let eI := serreIncidenceIdealIsoTransport q I
  have hi : eI.hom ≫ I.subschemeι ≫ pullback.fst b
      (toBase (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin n) K))) =
      I'.subschemeι ≫ pullback.fst b
        (toBase (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin 9) K))) := by
    rw [← Category.assoc, serreIncidenceIdealIsoTransport_subschemeι,
      Category.assoc, serreIncidenceProductRankIso_inv_fst]
  refine ⟨eP ≪≫ eI, ?_, ?_⟩
  · simp only [Iso.trans_hom, Category.assoc]
    rw [hi]
    exact hp
  · have hf : I.subschemeι ≫ pullback.fst b
        (toBase (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin n) K))) =
        eI.inv ≫ I'.subschemeι ≫ pullback.fst b
          (toBase (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin 9) K))) := by
      rw [← hi]
      simp
    rw [hf]
    exact hopen.comp eI.inv.isOpenMap

theorem serreThreePointSectionIncidence_exists_native_plane
    {K : Type u} [Field K] {X B : Scheme.{u}} [IsAffine B]
    (base : X ⟶ Spec (.of K)) [IsSeparated base] (M : X.Modules)
    [FiniteDimensional K (SchemeModuleGlobalSectionsOver base M)]
    (C : SchemeModuleFiniteFreeAffineCover M (ULift.{u} (Fin 2)))
    (b : B ⟶ Spec (.of K)) (chart : Fin 3 → C.ι)
    (markedU : ∀ i, B ⟶ (C.U (chart i) : Scheme.{u}))
    (hmarked : ∀ i, (markedU i ≫ (C.U (chart i)).ι) ≫ base = b)
    (h9 : Module.finrank K (SchemeModuleGlobalSectionsOver base M) = 9)
    (ρ : Fin 6 ≃ (Fin 3 × ULift.{u} (Fin 2)))
    (m : Fin 6 ↪ Fin 9)
    (hm : IsUnit (Matrix.submatrix (fun r k => serreIncidenceGlobalBasisEvaluationMatrix
      base M C chart markedU (ρ r) ((finCongr h9).symm k)) id m).det) :
    letI := C.isClosedImmersion_projectiveSectionLocalZeroGluedToAmbient base M
    let I := serreThreePointSectionIncidenceIdeal b base
      (schemeModuleGlobalSectionsProjectiveParametersToBase base M)
      (fun i => markedU i ≫ (C.U (chart i)).ι) hmarked
      (C.projectiveSectionLocalZeroGluedToAmbient base M)
    ∃ e : scheme (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin 3) Γ(B, ⊤))) ≅
        I.subscheme,
      e.hom ≫ I.subschemeι ≫ pullback.fst b
        (schemeModuleGlobalSectionsProjectiveParametersToBase base M) =
        toBase (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin 3) Γ(B, ⊤))) ≫
          B.isoSpec.inv ∧
      IsOpenMap (I.subschemeι ≫ pullback.fst b
        (schemeModuleGlobalSectionsProjectiveParametersToBase base M)) := by
  letI := C.isClosedImmersion_projectiveSectionLocalZeroGluedToAmbient base M
  exact serreIncidence_exists_plane_of_rank_rows_minor b h9 _
    (fun r k => serreIncidenceGlobalBasisEvaluationMatrix base M C chart markedU (ρ r) k)
    (fun j => serreThreePointSectionIncidenceIdeal_rank_rows
      base M C b chart markedU hmarked ρ j) m hm

end PfaffianDescent
