// Lean compiler output
// Module: PureLean.InductiveCompilers
// Imports: public import Init public meta import Init
#include <lean/lean.h>
#if defined(__clang__)
#pragma clang diagnostic ignored "-Wunused-parameter"
#pragma clang diagnostic ignored "-Wunused-label"
#elif defined(__GNUC__) && !defined(__CLANG__)
#pragma GCC diagnostic ignored "-Wunused-parameter"
#pragma GCC diagnostic ignored "-Wunused-label"
#pragma GCC diagnostic ignored "-Wunused-but-set-variable"
#endif
#ifdef __cplusplus
extern "C" {
#endif
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_obj_tag_nat(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* l_List_appendTR___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_purelean_PureLean_InductiveCompilers_Section01_BTree_ctorIdx___impl___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_purelean_PureLean_InductiveCompilers_Section01_BTree_ctorIdx___impl___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_purelean_PureLean_InductiveCompilers_Section01_BTree_ctorIdx___impl(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_purelean_PureLean_InductiveCompilers_Section01_BTree_ctorIdx___impl___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_purelean_PureLean_InductiveCompilers_Section01_BTree_ctorElim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_purelean_PureLean_InductiveCompilers_Section01_BTree_ctorElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_purelean_PureLean_InductiveCompilers_Section01_BTree_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_purelean_PureLean_InductiveCompilers_Section01_BTree_leaf_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_purelean_PureLean_InductiveCompilers_Section01_BTree_leaf_elim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_purelean_PureLean_InductiveCompilers_Section01_BTree_node_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_purelean_PureLean_InductiveCompilers_Section01_BTree_node_elim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_purelean_PureLean_InductiveCompilers_Section01_mirrorT___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_purelean_PureLean_InductiveCompilers_Section01_mirrorT(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_purelean_PureLean_InductiveCompilers_Section01_sizeT___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_purelean_PureLean_InductiveCompilers_Section01_sizeT___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_purelean_PureLean_InductiveCompilers_Section01_sizeT(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_purelean_PureLean_InductiveCompilers_Section01_sizeT___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_purelean_PureLean_InductiveCompilers_Section01_mapT___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_purelean_PureLean_InductiveCompilers_Section01_mapT(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_purelean_PureLean_InductiveCompilers_Section02_sumL2(lean_object*);
LEAN_EXPORT lean_object* lp_purelean_PureLean_InductiveCompilers_Section02_sumL2___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_purelean_PureLean_InductiveCompilers_Section02_sumAcc(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_purelean_PureLean_InductiveCompilers_Section02_sumAcc___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_purelean_PureLean_InductiveCompilers_Section02_revAcc___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_purelean_PureLean_InductiveCompilers_Section02_revAcc(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_purelean_PureLean_InductiveCompilers_Section02_filterL___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_purelean_PureLean_InductiveCompilers_Section02_filterL(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_purelean_PureLean_InductiveCompilers_Section02_foldrL___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_purelean_PureLean_InductiveCompilers_Section02_foldrL___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_purelean_PureLean_InductiveCompilers_Section02_foldrL(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_purelean_PureLean_InductiveCompilers_Section02_foldrL___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_purelean_PureLean_InductiveCompilers_Section03_snocL___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_purelean_PureLean_InductiveCompilers_Section03_snocL(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_purelean_PureLean_InductiveCompilers_Section03_revL___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_purelean_PureLean_InductiveCompilers_Section03_revL(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_purelean_PureLean_InductiveCompilers_Section03_mapL___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_purelean_PureLean_InductiveCompilers_Section03_mapL(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_purelean_PureLean_InductiveCompilers_Section03_sumL(lean_object*);
LEAN_EXPORT lean_object* lp_purelean_PureLean_InductiveCompilers_Section03_sumL___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_purelean_PureLean_InductiveCompilers_Section04_FullTree_ctorIdx___impl___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_purelean_PureLean_InductiveCompilers_Section04_FullTree_ctorIdx___impl___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_purelean_PureLean_InductiveCompilers_Section04_FullTree_ctorIdx___impl(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_purelean_PureLean_InductiveCompilers_Section04_FullTree_ctorIdx___impl___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_purelean_PureLean_InductiveCompilers_Section04_FullTree_ctorElim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_purelean_PureLean_InductiveCompilers_Section04_FullTree_ctorElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_purelean_PureLean_InductiveCompilers_Section04_FullTree_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_purelean_PureLean_InductiveCompilers_Section04_FullTree_tip_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_purelean_PureLean_InductiveCompilers_Section04_FullTree_tip_elim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_purelean_PureLean_InductiveCompilers_Section04_FullTree_fork_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_purelean_PureLean_InductiveCompilers_Section04_FullTree_fork_elim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_purelean_PureLean_InductiveCompilers_Section04_leavesFT___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_purelean_PureLean_InductiveCompilers_Section04_leavesFT___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_purelean_PureLean_InductiveCompilers_Section04_leavesFT(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_purelean_PureLean_InductiveCompilers_Section04_leavesFT___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_purelean_PureLean_InductiveCompilers_Section04_forksFT___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_purelean_PureLean_InductiveCompilers_Section04_forksFT___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_purelean_PureLean_InductiveCompilers_Section04_forksFT(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_purelean_PureLean_InductiveCompilers_Section04_forksFT___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_purelean_PureLean_InductiveCompilers_Section04_flipFT___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_purelean_PureLean_InductiveCompilers_Section04_flipFT(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_purelean_PureLean_InductiveCompilers_Section05_AddExpr_ctorIdx___impl(lean_object*);
LEAN_EXPORT lean_object* lp_purelean_PureLean_InductiveCompilers_Section05_AddExpr_ctorIdx___impl___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_purelean_PureLean_InductiveCompilers_Section05_AddExpr_ctorElim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_purelean_PureLean_InductiveCompilers_Section05_AddExpr_ctorElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_purelean_PureLean_InductiveCompilers_Section05_AddExpr_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_purelean_PureLean_InductiveCompilers_Section05_AddExpr_lit_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_purelean_PureLean_InductiveCompilers_Section05_AddExpr_lit_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_purelean_PureLean_InductiveCompilers_Section05_AddExpr_add_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_purelean_PureLean_InductiveCompilers_Section05_AddExpr_add_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_purelean_PureLean_InductiveCompilers_Section05_evalAdd(lean_object*);
LEAN_EXPORT lean_object* lp_purelean_PureLean_InductiveCompilers_Section05_evalAdd___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_purelean_PureLean_InductiveCompilers_Section05_VMInstr_ctorIdx___impl(lean_object*);
LEAN_EXPORT lean_object* lp_purelean_PureLean_InductiveCompilers_Section05_VMInstr_ctorIdx___impl___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_purelean_PureLean_InductiveCompilers_Section05_VMInstr_ctorElim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_purelean_PureLean_InductiveCompilers_Section05_VMInstr_ctorElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_purelean_PureLean_InductiveCompilers_Section05_VMInstr_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_purelean_PureLean_InductiveCompilers_Section05_VMInstr_push_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_purelean_PureLean_InductiveCompilers_Section05_VMInstr_push_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_purelean_PureLean_InductiveCompilers_Section05_VMInstr_addTop_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_purelean_PureLean_InductiveCompilers_Section05_VMInstr_addTop_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_purelean_PureLean_InductiveCompilers_Section05_runVM(lean_object*, lean_object*);
static const lean_ctor_object lp_purelean_PureLean_InductiveCompilers_Section05_compileAdd___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(1) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* lp_purelean_PureLean_InductiveCompilers_Section05_compileAdd___closed__0 = (const lean_object*)&lp_purelean_PureLean_InductiveCompilers_Section05_compileAdd___closed__0_value;
LEAN_EXPORT lean_object* lp_purelean_PureLean_InductiveCompilers_Section05_compileAdd(lean_object*);
LEAN_EXPORT lean_object* lp_purelean_PureLean_InductiveCompilers_Section06_PureExpr_ctorIdx___impl(lean_object*);
LEAN_EXPORT lean_object* lp_purelean_PureLean_InductiveCompilers_Section06_PureExpr_ctorIdx___impl___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_purelean_PureLean_InductiveCompilers_Section06_PureExpr_ctorElim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_purelean_PureLean_InductiveCompilers_Section06_PureExpr_ctorElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_purelean_PureLean_InductiveCompilers_Section06_PureExpr_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_purelean_PureLean_InductiveCompilers_Section06_PureExpr_lit_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_purelean_PureLean_InductiveCompilers_Section06_PureExpr_lit_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_purelean_PureLean_InductiveCompilers_Section06_PureExpr_var_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_purelean_PureLean_InductiveCompilers_Section06_PureExpr_var_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_purelean_PureLean_InductiveCompilers_Section06_PureExpr_add_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_purelean_PureLean_InductiveCompilers_Section06_PureExpr_add_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_purelean_PureLean_InductiveCompilers_Section06_PureExpr_mul_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_purelean_PureLean_InductiveCompilers_Section06_PureExpr_mul_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_purelean_PureLean_InductiveCompilers_Section06_evalExpr(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_purelean_PureLean_InductiveCompilers_Section06_swapAddExpr(lean_object*);
LEAN_EXPORT lean_object* lp_purelean_PureLean_InductiveCompilers_Section06_optZeroExpr(lean_object*);
LEAN_EXPORT lean_object* lp_purelean_PureLean_InductiveCompilers_Section01_BTree_ctorIdx___impl___redArg(lean_object* v_x_1_){
_start:
{
lean_object* v___x_2_; 
v___x_2_ = lean_obj_tag_nat(v_x_1_);
return v___x_2_;
}
}
LEAN_EXPORT lean_object* lp_purelean_PureLean_InductiveCompilers_Section01_BTree_ctorIdx___impl___redArg___boxed(lean_object* v_x_3_){
_start:
{
lean_object* v_res_4_; 
v_res_4_ = lp_purelean_PureLean_InductiveCompilers_Section01_BTree_ctorIdx___impl___redArg(v_x_3_);
lean_dec(v_x_3_);
return v_res_4_;
}
}
LEAN_EXPORT lean_object* lp_purelean_PureLean_InductiveCompilers_Section01_BTree_ctorIdx___impl(lean_object* v_00_u03b1_5_, lean_object* v_x_6_){
_start:
{
lean_object* v___x_7_; 
v___x_7_ = lean_obj_tag_nat(v_x_6_);
return v___x_7_;
}
}
LEAN_EXPORT lean_object* lp_purelean_PureLean_InductiveCompilers_Section01_BTree_ctorIdx___impl___boxed(lean_object* v_00_u03b1_8_, lean_object* v_x_9_){
_start:
{
lean_object* v_res_10_; 
v_res_10_ = lp_purelean_PureLean_InductiveCompilers_Section01_BTree_ctorIdx___impl(v_00_u03b1_8_, v_x_9_);
lean_dec(v_x_9_);
return v_res_10_;
}
}
LEAN_EXPORT lean_object* lp_purelean_PureLean_InductiveCompilers_Section01_BTree_ctorElim___redArg(lean_object* v_t_11_, lean_object* v_k_12_){
_start:
{
if (lean_obj_tag(v_t_11_) == 0)
{
return v_k_12_;
}
else
{
lean_object* v_a_13_; lean_object* v_a_14_; lean_object* v_a_15_; lean_object* v___x_16_; 
v_a_13_ = lean_ctor_get(v_t_11_, 0);
lean_inc(v_a_13_);
v_a_14_ = lean_ctor_get(v_t_11_, 1);
lean_inc(v_a_14_);
v_a_15_ = lean_ctor_get(v_t_11_, 2);
lean_inc(v_a_15_);
lean_dec_ref_known(v_t_11_, 3);
v___x_16_ = lean_apply_3(v_k_12_, v_a_13_, v_a_14_, v_a_15_);
return v___x_16_;
}
}
}
LEAN_EXPORT lean_object* lp_purelean_PureLean_InductiveCompilers_Section01_BTree_ctorElim(lean_object* v_00_u03b1_17_, lean_object* v_motive_18_, lean_object* v_ctorIdx_19_, lean_object* v_t_20_, lean_object* v_h_21_, lean_object* v_k_22_){
_start:
{
lean_object* v___x_23_; 
v___x_23_ = lp_purelean_PureLean_InductiveCompilers_Section01_BTree_ctorElim___redArg(v_t_20_, v_k_22_);
return v___x_23_;
}
}
LEAN_EXPORT lean_object* lp_purelean_PureLean_InductiveCompilers_Section01_BTree_ctorElim___boxed(lean_object* v_00_u03b1_24_, lean_object* v_motive_25_, lean_object* v_ctorIdx_26_, lean_object* v_t_27_, lean_object* v_h_28_, lean_object* v_k_29_){
_start:
{
lean_object* v_res_30_; 
v_res_30_ = lp_purelean_PureLean_InductiveCompilers_Section01_BTree_ctorElim(v_00_u03b1_24_, v_motive_25_, v_ctorIdx_26_, v_t_27_, v_h_28_, v_k_29_);
lean_dec(v_ctorIdx_26_);
return v_res_30_;
}
}
LEAN_EXPORT lean_object* lp_purelean_PureLean_InductiveCompilers_Section01_BTree_leaf_elim___redArg(lean_object* v_t_31_, lean_object* v_leaf_32_){
_start:
{
lean_object* v___x_33_; 
v___x_33_ = lp_purelean_PureLean_InductiveCompilers_Section01_BTree_ctorElim___redArg(v_t_31_, v_leaf_32_);
return v___x_33_;
}
}
LEAN_EXPORT lean_object* lp_purelean_PureLean_InductiveCompilers_Section01_BTree_leaf_elim(lean_object* v_00_u03b1_34_, lean_object* v_motive_35_, lean_object* v_t_36_, lean_object* v_h_37_, lean_object* v_leaf_38_){
_start:
{
lean_object* v___x_39_; 
v___x_39_ = lp_purelean_PureLean_InductiveCompilers_Section01_BTree_ctorElim___redArg(v_t_36_, v_leaf_38_);
return v___x_39_;
}
}
LEAN_EXPORT lean_object* lp_purelean_PureLean_InductiveCompilers_Section01_BTree_node_elim___redArg(lean_object* v_t_40_, lean_object* v_node_41_){
_start:
{
lean_object* v___x_42_; 
v___x_42_ = lp_purelean_PureLean_InductiveCompilers_Section01_BTree_ctorElim___redArg(v_t_40_, v_node_41_);
return v___x_42_;
}
}
LEAN_EXPORT lean_object* lp_purelean_PureLean_InductiveCompilers_Section01_BTree_node_elim(lean_object* v_00_u03b1_43_, lean_object* v_motive_44_, lean_object* v_t_45_, lean_object* v_h_46_, lean_object* v_node_47_){
_start:
{
lean_object* v___x_48_; 
v___x_48_ = lp_purelean_PureLean_InductiveCompilers_Section01_BTree_ctorElim___redArg(v_t_45_, v_node_47_);
return v___x_48_;
}
}
LEAN_EXPORT lean_object* lp_purelean_PureLean_InductiveCompilers_Section01_mirrorT___redArg(lean_object* v_x_49_){
_start:
{
if (lean_obj_tag(v_x_49_) == 0)
{
return v_x_49_;
}
else
{
lean_object* v_a_50_; lean_object* v_a_51_; lean_object* v_a_52_; lean_object* v___x_54_; uint8_t v_isShared_55_; uint8_t v_isSharedCheck_61_; 
v_a_50_ = lean_ctor_get(v_x_49_, 0);
v_a_51_ = lean_ctor_get(v_x_49_, 1);
v_a_52_ = lean_ctor_get(v_x_49_, 2);
v_isSharedCheck_61_ = !lean_is_exclusive(v_x_49_);
if (v_isSharedCheck_61_ == 0)
{
v___x_54_ = v_x_49_;
v_isShared_55_ = v_isSharedCheck_61_;
goto v_resetjp_53_;
}
else
{
lean_inc(v_a_52_);
lean_inc(v_a_51_);
lean_inc(v_a_50_);
lean_dec(v_x_49_);
v___x_54_ = lean_box(0);
v_isShared_55_ = v_isSharedCheck_61_;
goto v_resetjp_53_;
}
v_resetjp_53_:
{
lean_object* v___x_56_; lean_object* v___x_57_; lean_object* v___x_59_; 
v___x_56_ = lp_purelean_PureLean_InductiveCompilers_Section01_mirrorT___redArg(v_a_52_);
v___x_57_ = lp_purelean_PureLean_InductiveCompilers_Section01_mirrorT___redArg(v_a_50_);
if (v_isShared_55_ == 0)
{
lean_ctor_set(v___x_54_, 2, v___x_57_);
lean_ctor_set(v___x_54_, 0, v___x_56_);
v___x_59_ = v___x_54_;
goto v_reusejp_58_;
}
else
{
lean_object* v_reuseFailAlloc_60_; 
v_reuseFailAlloc_60_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_60_, 0, v___x_56_);
lean_ctor_set(v_reuseFailAlloc_60_, 1, v_a_51_);
lean_ctor_set(v_reuseFailAlloc_60_, 2, v___x_57_);
v___x_59_ = v_reuseFailAlloc_60_;
goto v_reusejp_58_;
}
v_reusejp_58_:
{
return v___x_59_;
}
}
}
}
}
LEAN_EXPORT lean_object* lp_purelean_PureLean_InductiveCompilers_Section01_mirrorT(lean_object* v_00_u03b1_62_, lean_object* v_x_63_){
_start:
{
lean_object* v___x_64_; 
v___x_64_ = lp_purelean_PureLean_InductiveCompilers_Section01_mirrorT___redArg(v_x_63_);
return v___x_64_;
}
}
LEAN_EXPORT lean_object* lp_purelean_PureLean_InductiveCompilers_Section01_sizeT___redArg(lean_object* v_x_65_){
_start:
{
if (lean_obj_tag(v_x_65_) == 0)
{
lean_object* v___x_66_; 
v___x_66_ = lean_unsigned_to_nat(0u);
return v___x_66_;
}
else
{
lean_object* v_a_67_; lean_object* v_a_68_; lean_object* v___x_69_; lean_object* v___x_70_; lean_object* v___x_71_; lean_object* v___x_72_; lean_object* v___x_73_; 
v_a_67_ = lean_ctor_get(v_x_65_, 0);
v_a_68_ = lean_ctor_get(v_x_65_, 2);
v___x_69_ = lean_unsigned_to_nat(1u);
v___x_70_ = lp_purelean_PureLean_InductiveCompilers_Section01_sizeT___redArg(v_a_67_);
v___x_71_ = lean_nat_add(v___x_69_, v___x_70_);
lean_dec(v___x_70_);
v___x_72_ = lp_purelean_PureLean_InductiveCompilers_Section01_sizeT___redArg(v_a_68_);
v___x_73_ = lean_nat_add(v___x_71_, v___x_72_);
lean_dec(v___x_72_);
lean_dec(v___x_71_);
return v___x_73_;
}
}
}
LEAN_EXPORT lean_object* lp_purelean_PureLean_InductiveCompilers_Section01_sizeT___redArg___boxed(lean_object* v_x_74_){
_start:
{
lean_object* v_res_75_; 
v_res_75_ = lp_purelean_PureLean_InductiveCompilers_Section01_sizeT___redArg(v_x_74_);
lean_dec(v_x_74_);
return v_res_75_;
}
}
LEAN_EXPORT lean_object* lp_purelean_PureLean_InductiveCompilers_Section01_sizeT(lean_object* v_00_u03b1_76_, lean_object* v_x_77_){
_start:
{
lean_object* v___x_78_; 
v___x_78_ = lp_purelean_PureLean_InductiveCompilers_Section01_sizeT___redArg(v_x_77_);
return v___x_78_;
}
}
LEAN_EXPORT lean_object* lp_purelean_PureLean_InductiveCompilers_Section01_sizeT___boxed(lean_object* v_00_u03b1_79_, lean_object* v_x_80_){
_start:
{
lean_object* v_res_81_; 
v_res_81_ = lp_purelean_PureLean_InductiveCompilers_Section01_sizeT(v_00_u03b1_79_, v_x_80_);
lean_dec(v_x_80_);
return v_res_81_;
}
}
LEAN_EXPORT lean_object* lp_purelean_PureLean_InductiveCompilers_Section01_mapT___redArg(lean_object* v_f_82_, lean_object* v_x_83_){
_start:
{
if (lean_obj_tag(v_x_83_) == 0)
{
lean_object* v___x_84_; 
lean_dec(v_f_82_);
v___x_84_ = lean_box(0);
return v___x_84_;
}
else
{
lean_object* v_a_85_; lean_object* v_a_86_; lean_object* v_a_87_; lean_object* v___x_89_; uint8_t v_isShared_90_; uint8_t v_isSharedCheck_97_; 
v_a_85_ = lean_ctor_get(v_x_83_, 0);
v_a_86_ = lean_ctor_get(v_x_83_, 1);
v_a_87_ = lean_ctor_get(v_x_83_, 2);
v_isSharedCheck_97_ = !lean_is_exclusive(v_x_83_);
if (v_isSharedCheck_97_ == 0)
{
v___x_89_ = v_x_83_;
v_isShared_90_ = v_isSharedCheck_97_;
goto v_resetjp_88_;
}
else
{
lean_inc(v_a_87_);
lean_inc(v_a_86_);
lean_inc(v_a_85_);
lean_dec(v_x_83_);
v___x_89_ = lean_box(0);
v_isShared_90_ = v_isSharedCheck_97_;
goto v_resetjp_88_;
}
v_resetjp_88_:
{
lean_object* v___x_91_; lean_object* v___x_92_; lean_object* v___x_93_; lean_object* v___x_95_; 
lean_inc_n(v_f_82_, 2);
v___x_91_ = lp_purelean_PureLean_InductiveCompilers_Section01_mapT___redArg(v_f_82_, v_a_85_);
v___x_92_ = lean_apply_1(v_f_82_, v_a_86_);
v___x_93_ = lp_purelean_PureLean_InductiveCompilers_Section01_mapT___redArg(v_f_82_, v_a_87_);
if (v_isShared_90_ == 0)
{
lean_ctor_set(v___x_89_, 2, v___x_93_);
lean_ctor_set(v___x_89_, 1, v___x_92_);
lean_ctor_set(v___x_89_, 0, v___x_91_);
v___x_95_ = v___x_89_;
goto v_reusejp_94_;
}
else
{
lean_object* v_reuseFailAlloc_96_; 
v_reuseFailAlloc_96_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_96_, 0, v___x_91_);
lean_ctor_set(v_reuseFailAlloc_96_, 1, v___x_92_);
lean_ctor_set(v_reuseFailAlloc_96_, 2, v___x_93_);
v___x_95_ = v_reuseFailAlloc_96_;
goto v_reusejp_94_;
}
v_reusejp_94_:
{
return v___x_95_;
}
}
}
}
}
LEAN_EXPORT lean_object* lp_purelean_PureLean_InductiveCompilers_Section01_mapT(lean_object* v_00_u03b1_98_, lean_object* v_00_u03b2_99_, lean_object* v_f_100_, lean_object* v_x_101_){
_start:
{
lean_object* v___x_102_; 
v___x_102_ = lp_purelean_PureLean_InductiveCompilers_Section01_mapT___redArg(v_f_100_, v_x_101_);
return v___x_102_;
}
}
LEAN_EXPORT lean_object* lp_purelean_PureLean_InductiveCompilers_Section02_sumL2(lean_object* v_x_103_){
_start:
{
if (lean_obj_tag(v_x_103_) == 0)
{
lean_object* v___x_104_; 
v___x_104_ = lean_unsigned_to_nat(0u);
return v___x_104_;
}
else
{
lean_object* v_head_105_; lean_object* v_tail_106_; lean_object* v___x_107_; lean_object* v___x_108_; 
v_head_105_ = lean_ctor_get(v_x_103_, 0);
v_tail_106_ = lean_ctor_get(v_x_103_, 1);
v___x_107_ = lp_purelean_PureLean_InductiveCompilers_Section02_sumL2(v_tail_106_);
v___x_108_ = lean_nat_add(v_head_105_, v___x_107_);
lean_dec(v___x_107_);
return v___x_108_;
}
}
}
LEAN_EXPORT lean_object* lp_purelean_PureLean_InductiveCompilers_Section02_sumL2___boxed(lean_object* v_x_109_){
_start:
{
lean_object* v_res_110_; 
v_res_110_ = lp_purelean_PureLean_InductiveCompilers_Section02_sumL2(v_x_109_);
lean_dec(v_x_109_);
return v_res_110_;
}
}
LEAN_EXPORT lean_object* lp_purelean_PureLean_InductiveCompilers_Section02_sumAcc(lean_object* v_x_111_, lean_object* v_x_112_){
_start:
{
if (lean_obj_tag(v_x_111_) == 0)
{
return v_x_112_;
}
else
{
lean_object* v_head_113_; lean_object* v_tail_114_; lean_object* v___x_115_; 
v_head_113_ = lean_ctor_get(v_x_111_, 0);
v_tail_114_ = lean_ctor_get(v_x_111_, 1);
v___x_115_ = lean_nat_add(v_x_112_, v_head_113_);
lean_dec(v_x_112_);
v_x_111_ = v_tail_114_;
v_x_112_ = v___x_115_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* lp_purelean_PureLean_InductiveCompilers_Section02_sumAcc___boxed(lean_object* v_x_117_, lean_object* v_x_118_){
_start:
{
lean_object* v_res_119_; 
v_res_119_ = lp_purelean_PureLean_InductiveCompilers_Section02_sumAcc(v_x_117_, v_x_118_);
lean_dec(v_x_117_);
return v_res_119_;
}
}
LEAN_EXPORT lean_object* lp_purelean_PureLean_InductiveCompilers_Section02_revAcc___redArg(lean_object* v_x_120_, lean_object* v_x_121_){
_start:
{
if (lean_obj_tag(v_x_120_) == 0)
{
return v_x_121_;
}
else
{
lean_object* v_head_122_; lean_object* v_tail_123_; lean_object* v___x_125_; uint8_t v_isShared_126_; uint8_t v_isSharedCheck_131_; 
v_head_122_ = lean_ctor_get(v_x_120_, 0);
v_tail_123_ = lean_ctor_get(v_x_120_, 1);
v_isSharedCheck_131_ = !lean_is_exclusive(v_x_120_);
if (v_isSharedCheck_131_ == 0)
{
v___x_125_ = v_x_120_;
v_isShared_126_ = v_isSharedCheck_131_;
goto v_resetjp_124_;
}
else
{
lean_inc(v_tail_123_);
lean_inc(v_head_122_);
lean_dec(v_x_120_);
v___x_125_ = lean_box(0);
v_isShared_126_ = v_isSharedCheck_131_;
goto v_resetjp_124_;
}
v_resetjp_124_:
{
lean_object* v___x_128_; 
if (v_isShared_126_ == 0)
{
lean_ctor_set(v___x_125_, 1, v_x_121_);
v___x_128_ = v___x_125_;
goto v_reusejp_127_;
}
else
{
lean_object* v_reuseFailAlloc_130_; 
v_reuseFailAlloc_130_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_130_, 0, v_head_122_);
lean_ctor_set(v_reuseFailAlloc_130_, 1, v_x_121_);
v___x_128_ = v_reuseFailAlloc_130_;
goto v_reusejp_127_;
}
v_reusejp_127_:
{
v_x_120_ = v_tail_123_;
v_x_121_ = v___x_128_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* lp_purelean_PureLean_InductiveCompilers_Section02_revAcc(lean_object* v_00_u03b1_132_, lean_object* v_x_133_, lean_object* v_x_134_){
_start:
{
lean_object* v___x_135_; 
v___x_135_ = lp_purelean_PureLean_InductiveCompilers_Section02_revAcc___redArg(v_x_133_, v_x_134_);
return v___x_135_;
}
}
LEAN_EXPORT lean_object* lp_purelean_PureLean_InductiveCompilers_Section02_filterL___redArg(lean_object* v_p_136_, lean_object* v_x_137_){
_start:
{
if (lean_obj_tag(v_x_137_) == 0)
{
lean_dec_ref(v_p_136_);
return v_x_137_;
}
else
{
lean_object* v_head_138_; lean_object* v_tail_139_; lean_object* v___x_141_; uint8_t v_isShared_142_; uint8_t v_isSharedCheck_150_; 
v_head_138_ = lean_ctor_get(v_x_137_, 0);
v_tail_139_ = lean_ctor_get(v_x_137_, 1);
v_isSharedCheck_150_ = !lean_is_exclusive(v_x_137_);
if (v_isSharedCheck_150_ == 0)
{
v___x_141_ = v_x_137_;
v_isShared_142_ = v_isSharedCheck_150_;
goto v_resetjp_140_;
}
else
{
lean_inc(v_tail_139_);
lean_inc(v_head_138_);
lean_dec(v_x_137_);
v___x_141_ = lean_box(0);
v_isShared_142_ = v_isSharedCheck_150_;
goto v_resetjp_140_;
}
v_resetjp_140_:
{
lean_object* v___x_143_; uint8_t v___x_144_; 
lean_inc_ref(v_p_136_);
lean_inc(v_head_138_);
v___x_143_ = lean_apply_1(v_p_136_, v_head_138_);
v___x_144_ = lean_unbox(v___x_143_);
if (v___x_144_ == 0)
{
lean_del_object(v___x_141_);
lean_dec(v_head_138_);
v_x_137_ = v_tail_139_;
goto _start;
}
else
{
lean_object* v___x_146_; lean_object* v___x_148_; 
v___x_146_ = lp_purelean_PureLean_InductiveCompilers_Section02_filterL___redArg(v_p_136_, v_tail_139_);
if (v_isShared_142_ == 0)
{
lean_ctor_set(v___x_141_, 1, v___x_146_);
v___x_148_ = v___x_141_;
goto v_reusejp_147_;
}
else
{
lean_object* v_reuseFailAlloc_149_; 
v_reuseFailAlloc_149_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_149_, 0, v_head_138_);
lean_ctor_set(v_reuseFailAlloc_149_, 1, v___x_146_);
v___x_148_ = v_reuseFailAlloc_149_;
goto v_reusejp_147_;
}
v_reusejp_147_:
{
return v___x_148_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* lp_purelean_PureLean_InductiveCompilers_Section02_filterL(lean_object* v_00_u03b1_151_, lean_object* v_p_152_, lean_object* v_x_153_){
_start:
{
lean_object* v___x_154_; 
v___x_154_ = lp_purelean_PureLean_InductiveCompilers_Section02_filterL___redArg(v_p_152_, v_x_153_);
return v___x_154_;
}
}
LEAN_EXPORT lean_object* lp_purelean_PureLean_InductiveCompilers_Section02_foldrL___redArg(lean_object* v_f_155_, lean_object* v_z_156_, lean_object* v_x_157_){
_start:
{
if (lean_obj_tag(v_x_157_) == 0)
{
lean_dec(v_f_155_);
lean_inc(v_z_156_);
return v_z_156_;
}
else
{
lean_object* v_head_158_; lean_object* v_tail_159_; lean_object* v___x_160_; lean_object* v___x_161_; 
v_head_158_ = lean_ctor_get(v_x_157_, 0);
lean_inc(v_head_158_);
v_tail_159_ = lean_ctor_get(v_x_157_, 1);
lean_inc(v_tail_159_);
lean_dec_ref_known(v_x_157_, 2);
lean_inc(v_f_155_);
v___x_160_ = lp_purelean_PureLean_InductiveCompilers_Section02_foldrL___redArg(v_f_155_, v_z_156_, v_tail_159_);
v___x_161_ = lean_apply_2(v_f_155_, v_head_158_, v___x_160_);
return v___x_161_;
}
}
}
LEAN_EXPORT lean_object* lp_purelean_PureLean_InductiveCompilers_Section02_foldrL___redArg___boxed(lean_object* v_f_162_, lean_object* v_z_163_, lean_object* v_x_164_){
_start:
{
lean_object* v_res_165_; 
v_res_165_ = lp_purelean_PureLean_InductiveCompilers_Section02_foldrL___redArg(v_f_162_, v_z_163_, v_x_164_);
lean_dec(v_z_163_);
return v_res_165_;
}
}
LEAN_EXPORT lean_object* lp_purelean_PureLean_InductiveCompilers_Section02_foldrL(lean_object* v_00_u03b1_166_, lean_object* v_00_u03b2_167_, lean_object* v_f_168_, lean_object* v_z_169_, lean_object* v_x_170_){
_start:
{
lean_object* v___x_171_; 
v___x_171_ = lp_purelean_PureLean_InductiveCompilers_Section02_foldrL___redArg(v_f_168_, v_z_169_, v_x_170_);
return v___x_171_;
}
}
LEAN_EXPORT lean_object* lp_purelean_PureLean_InductiveCompilers_Section02_foldrL___boxed(lean_object* v_00_u03b1_172_, lean_object* v_00_u03b2_173_, lean_object* v_f_174_, lean_object* v_z_175_, lean_object* v_x_176_){
_start:
{
lean_object* v_res_177_; 
v_res_177_ = lp_purelean_PureLean_InductiveCompilers_Section02_foldrL(v_00_u03b1_172_, v_00_u03b2_173_, v_f_174_, v_z_175_, v_x_176_);
lean_dec(v_z_175_);
return v_res_177_;
}
}
LEAN_EXPORT lean_object* lp_purelean_PureLean_InductiveCompilers_Section03_snocL___redArg(lean_object* v_x_178_, lean_object* v_x_179_){
_start:
{
if (lean_obj_tag(v_x_178_) == 0)
{
lean_object* v___x_180_; 
v___x_180_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_180_, 0, v_x_179_);
lean_ctor_set(v___x_180_, 1, v_x_178_);
return v___x_180_;
}
else
{
lean_object* v_head_181_; lean_object* v_tail_182_; lean_object* v___x_184_; uint8_t v_isShared_185_; uint8_t v_isSharedCheck_190_; 
v_head_181_ = lean_ctor_get(v_x_178_, 0);
v_tail_182_ = lean_ctor_get(v_x_178_, 1);
v_isSharedCheck_190_ = !lean_is_exclusive(v_x_178_);
if (v_isSharedCheck_190_ == 0)
{
v___x_184_ = v_x_178_;
v_isShared_185_ = v_isSharedCheck_190_;
goto v_resetjp_183_;
}
else
{
lean_inc(v_tail_182_);
lean_inc(v_head_181_);
lean_dec(v_x_178_);
v___x_184_ = lean_box(0);
v_isShared_185_ = v_isSharedCheck_190_;
goto v_resetjp_183_;
}
v_resetjp_183_:
{
lean_object* v___x_186_; lean_object* v___x_188_; 
v___x_186_ = lp_purelean_PureLean_InductiveCompilers_Section03_snocL___redArg(v_tail_182_, v_x_179_);
if (v_isShared_185_ == 0)
{
lean_ctor_set(v___x_184_, 1, v___x_186_);
v___x_188_ = v___x_184_;
goto v_reusejp_187_;
}
else
{
lean_object* v_reuseFailAlloc_189_; 
v_reuseFailAlloc_189_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_189_, 0, v_head_181_);
lean_ctor_set(v_reuseFailAlloc_189_, 1, v___x_186_);
v___x_188_ = v_reuseFailAlloc_189_;
goto v_reusejp_187_;
}
v_reusejp_187_:
{
return v___x_188_;
}
}
}
}
}
LEAN_EXPORT lean_object* lp_purelean_PureLean_InductiveCompilers_Section03_snocL(lean_object* v_00_u03b1_191_, lean_object* v_x_192_, lean_object* v_x_193_){
_start:
{
lean_object* v___x_194_; 
v___x_194_ = lp_purelean_PureLean_InductiveCompilers_Section03_snocL___redArg(v_x_192_, v_x_193_);
return v___x_194_;
}
}
LEAN_EXPORT lean_object* lp_purelean_PureLean_InductiveCompilers_Section03_revL___redArg(lean_object* v_x_195_){
_start:
{
if (lean_obj_tag(v_x_195_) == 0)
{
return v_x_195_;
}
else
{
lean_object* v_head_196_; lean_object* v_tail_197_; lean_object* v___x_198_; lean_object* v___x_199_; 
v_head_196_ = lean_ctor_get(v_x_195_, 0);
lean_inc(v_head_196_);
v_tail_197_ = lean_ctor_get(v_x_195_, 1);
lean_inc(v_tail_197_);
lean_dec_ref_known(v_x_195_, 2);
v___x_198_ = lp_purelean_PureLean_InductiveCompilers_Section03_revL___redArg(v_tail_197_);
v___x_199_ = lp_purelean_PureLean_InductiveCompilers_Section03_snocL___redArg(v___x_198_, v_head_196_);
return v___x_199_;
}
}
}
LEAN_EXPORT lean_object* lp_purelean_PureLean_InductiveCompilers_Section03_revL(lean_object* v_00_u03b1_200_, lean_object* v_x_201_){
_start:
{
lean_object* v___x_202_; 
v___x_202_ = lp_purelean_PureLean_InductiveCompilers_Section03_revL___redArg(v_x_201_);
return v___x_202_;
}
}
LEAN_EXPORT lean_object* lp_purelean_PureLean_InductiveCompilers_Section03_mapL___redArg(lean_object* v_f_203_, lean_object* v_x_204_){
_start:
{
if (lean_obj_tag(v_x_204_) == 0)
{
lean_object* v___x_205_; 
lean_dec(v_f_203_);
v___x_205_ = lean_box(0);
return v___x_205_;
}
else
{
lean_object* v_head_206_; lean_object* v_tail_207_; lean_object* v___x_209_; uint8_t v_isShared_210_; uint8_t v_isSharedCheck_216_; 
v_head_206_ = lean_ctor_get(v_x_204_, 0);
v_tail_207_ = lean_ctor_get(v_x_204_, 1);
v_isSharedCheck_216_ = !lean_is_exclusive(v_x_204_);
if (v_isSharedCheck_216_ == 0)
{
v___x_209_ = v_x_204_;
v_isShared_210_ = v_isSharedCheck_216_;
goto v_resetjp_208_;
}
else
{
lean_inc(v_tail_207_);
lean_inc(v_head_206_);
lean_dec(v_x_204_);
v___x_209_ = lean_box(0);
v_isShared_210_ = v_isSharedCheck_216_;
goto v_resetjp_208_;
}
v_resetjp_208_:
{
lean_object* v___x_211_; lean_object* v___x_212_; lean_object* v___x_214_; 
lean_inc(v_f_203_);
v___x_211_ = lean_apply_1(v_f_203_, v_head_206_);
v___x_212_ = lp_purelean_PureLean_InductiveCompilers_Section03_mapL___redArg(v_f_203_, v_tail_207_);
if (v_isShared_210_ == 0)
{
lean_ctor_set(v___x_209_, 1, v___x_212_);
lean_ctor_set(v___x_209_, 0, v___x_211_);
v___x_214_ = v___x_209_;
goto v_reusejp_213_;
}
else
{
lean_object* v_reuseFailAlloc_215_; 
v_reuseFailAlloc_215_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_215_, 0, v___x_211_);
lean_ctor_set(v_reuseFailAlloc_215_, 1, v___x_212_);
v___x_214_ = v_reuseFailAlloc_215_;
goto v_reusejp_213_;
}
v_reusejp_213_:
{
return v___x_214_;
}
}
}
}
}
LEAN_EXPORT lean_object* lp_purelean_PureLean_InductiveCompilers_Section03_mapL(lean_object* v_00_u03b1_217_, lean_object* v_00_u03b2_218_, lean_object* v_f_219_, lean_object* v_x_220_){
_start:
{
lean_object* v___x_221_; 
v___x_221_ = lp_purelean_PureLean_InductiveCompilers_Section03_mapL___redArg(v_f_219_, v_x_220_);
return v___x_221_;
}
}
LEAN_EXPORT lean_object* lp_purelean_PureLean_InductiveCompilers_Section03_sumL(lean_object* v_x_222_){
_start:
{
if (lean_obj_tag(v_x_222_) == 0)
{
lean_object* v___x_223_; 
v___x_223_ = lean_unsigned_to_nat(0u);
return v___x_223_;
}
else
{
lean_object* v_head_224_; lean_object* v_tail_225_; lean_object* v___x_226_; lean_object* v___x_227_; 
v_head_224_ = lean_ctor_get(v_x_222_, 0);
v_tail_225_ = lean_ctor_get(v_x_222_, 1);
v___x_226_ = lp_purelean_PureLean_InductiveCompilers_Section03_sumL(v_tail_225_);
v___x_227_ = lean_nat_add(v_head_224_, v___x_226_);
lean_dec(v___x_226_);
return v___x_227_;
}
}
}
LEAN_EXPORT lean_object* lp_purelean_PureLean_InductiveCompilers_Section03_sumL___boxed(lean_object* v_x_228_){
_start:
{
lean_object* v_res_229_; 
v_res_229_ = lp_purelean_PureLean_InductiveCompilers_Section03_sumL(v_x_228_);
lean_dec(v_x_228_);
return v_res_229_;
}
}
LEAN_EXPORT lean_object* lp_purelean_PureLean_InductiveCompilers_Section04_FullTree_ctorIdx___impl___redArg(lean_object* v_x_230_){
_start:
{
lean_object* v___x_231_; 
v___x_231_ = lean_obj_tag_nat(v_x_230_);
return v___x_231_;
}
}
LEAN_EXPORT lean_object* lp_purelean_PureLean_InductiveCompilers_Section04_FullTree_ctorIdx___impl___redArg___boxed(lean_object* v_x_232_){
_start:
{
lean_object* v_res_233_; 
v_res_233_ = lp_purelean_PureLean_InductiveCompilers_Section04_FullTree_ctorIdx___impl___redArg(v_x_232_);
lean_dec_ref(v_x_232_);
return v_res_233_;
}
}
LEAN_EXPORT lean_object* lp_purelean_PureLean_InductiveCompilers_Section04_FullTree_ctorIdx___impl(lean_object* v_00_u03b1_234_, lean_object* v_x_235_){
_start:
{
lean_object* v___x_236_; 
v___x_236_ = lean_obj_tag_nat(v_x_235_);
return v___x_236_;
}
}
LEAN_EXPORT lean_object* lp_purelean_PureLean_InductiveCompilers_Section04_FullTree_ctorIdx___impl___boxed(lean_object* v_00_u03b1_237_, lean_object* v_x_238_){
_start:
{
lean_object* v_res_239_; 
v_res_239_ = lp_purelean_PureLean_InductiveCompilers_Section04_FullTree_ctorIdx___impl(v_00_u03b1_237_, v_x_238_);
lean_dec_ref(v_x_238_);
return v_res_239_;
}
}
LEAN_EXPORT lean_object* lp_purelean_PureLean_InductiveCompilers_Section04_FullTree_ctorElim___redArg(lean_object* v_t_240_, lean_object* v_k_241_){
_start:
{
if (lean_obj_tag(v_t_240_) == 0)
{
lean_object* v_a_242_; lean_object* v___x_243_; 
v_a_242_ = lean_ctor_get(v_t_240_, 0);
lean_inc(v_a_242_);
lean_dec_ref_known(v_t_240_, 1);
v___x_243_ = lean_apply_1(v_k_241_, v_a_242_);
return v___x_243_;
}
else
{
lean_object* v_a_244_; lean_object* v_a_245_; lean_object* v___x_246_; 
v_a_244_ = lean_ctor_get(v_t_240_, 0);
lean_inc_ref(v_a_244_);
v_a_245_ = lean_ctor_get(v_t_240_, 1);
lean_inc_ref(v_a_245_);
lean_dec_ref_known(v_t_240_, 2);
v___x_246_ = lean_apply_2(v_k_241_, v_a_244_, v_a_245_);
return v___x_246_;
}
}
}
LEAN_EXPORT lean_object* lp_purelean_PureLean_InductiveCompilers_Section04_FullTree_ctorElim(lean_object* v_00_u03b1_247_, lean_object* v_motive_248_, lean_object* v_ctorIdx_249_, lean_object* v_t_250_, lean_object* v_h_251_, lean_object* v_k_252_){
_start:
{
lean_object* v___x_253_; 
v___x_253_ = lp_purelean_PureLean_InductiveCompilers_Section04_FullTree_ctorElim___redArg(v_t_250_, v_k_252_);
return v___x_253_;
}
}
LEAN_EXPORT lean_object* lp_purelean_PureLean_InductiveCompilers_Section04_FullTree_ctorElim___boxed(lean_object* v_00_u03b1_254_, lean_object* v_motive_255_, lean_object* v_ctorIdx_256_, lean_object* v_t_257_, lean_object* v_h_258_, lean_object* v_k_259_){
_start:
{
lean_object* v_res_260_; 
v_res_260_ = lp_purelean_PureLean_InductiveCompilers_Section04_FullTree_ctorElim(v_00_u03b1_254_, v_motive_255_, v_ctorIdx_256_, v_t_257_, v_h_258_, v_k_259_);
lean_dec(v_ctorIdx_256_);
return v_res_260_;
}
}
LEAN_EXPORT lean_object* lp_purelean_PureLean_InductiveCompilers_Section04_FullTree_tip_elim___redArg(lean_object* v_t_261_, lean_object* v_tip_262_){
_start:
{
lean_object* v___x_263_; 
v___x_263_ = lp_purelean_PureLean_InductiveCompilers_Section04_FullTree_ctorElim___redArg(v_t_261_, v_tip_262_);
return v___x_263_;
}
}
LEAN_EXPORT lean_object* lp_purelean_PureLean_InductiveCompilers_Section04_FullTree_tip_elim(lean_object* v_00_u03b1_264_, lean_object* v_motive_265_, lean_object* v_t_266_, lean_object* v_h_267_, lean_object* v_tip_268_){
_start:
{
lean_object* v___x_269_; 
v___x_269_ = lp_purelean_PureLean_InductiveCompilers_Section04_FullTree_ctorElim___redArg(v_t_266_, v_tip_268_);
return v___x_269_;
}
}
LEAN_EXPORT lean_object* lp_purelean_PureLean_InductiveCompilers_Section04_FullTree_fork_elim___redArg(lean_object* v_t_270_, lean_object* v_fork_271_){
_start:
{
lean_object* v___x_272_; 
v___x_272_ = lp_purelean_PureLean_InductiveCompilers_Section04_FullTree_ctorElim___redArg(v_t_270_, v_fork_271_);
return v___x_272_;
}
}
LEAN_EXPORT lean_object* lp_purelean_PureLean_InductiveCompilers_Section04_FullTree_fork_elim(lean_object* v_00_u03b1_273_, lean_object* v_motive_274_, lean_object* v_t_275_, lean_object* v_h_276_, lean_object* v_fork_277_){
_start:
{
lean_object* v___x_278_; 
v___x_278_ = lp_purelean_PureLean_InductiveCompilers_Section04_FullTree_ctorElim___redArg(v_t_275_, v_fork_277_);
return v___x_278_;
}
}
LEAN_EXPORT lean_object* lp_purelean_PureLean_InductiveCompilers_Section04_leavesFT___redArg(lean_object* v_x_279_){
_start:
{
if (lean_obj_tag(v_x_279_) == 0)
{
lean_object* v___x_280_; 
v___x_280_ = lean_unsigned_to_nat(1u);
return v___x_280_;
}
else
{
lean_object* v_a_281_; lean_object* v_a_282_; lean_object* v___x_283_; lean_object* v___x_284_; lean_object* v___x_285_; 
v_a_281_ = lean_ctor_get(v_x_279_, 0);
v_a_282_ = lean_ctor_get(v_x_279_, 1);
v___x_283_ = lp_purelean_PureLean_InductiveCompilers_Section04_leavesFT___redArg(v_a_281_);
v___x_284_ = lp_purelean_PureLean_InductiveCompilers_Section04_leavesFT___redArg(v_a_282_);
v___x_285_ = lean_nat_add(v___x_283_, v___x_284_);
lean_dec(v___x_284_);
lean_dec(v___x_283_);
return v___x_285_;
}
}
}
LEAN_EXPORT lean_object* lp_purelean_PureLean_InductiveCompilers_Section04_leavesFT___redArg___boxed(lean_object* v_x_286_){
_start:
{
lean_object* v_res_287_; 
v_res_287_ = lp_purelean_PureLean_InductiveCompilers_Section04_leavesFT___redArg(v_x_286_);
lean_dec_ref(v_x_286_);
return v_res_287_;
}
}
LEAN_EXPORT lean_object* lp_purelean_PureLean_InductiveCompilers_Section04_leavesFT(lean_object* v_00_u03b1_288_, lean_object* v_x_289_){
_start:
{
lean_object* v___x_290_; 
v___x_290_ = lp_purelean_PureLean_InductiveCompilers_Section04_leavesFT___redArg(v_x_289_);
return v___x_290_;
}
}
LEAN_EXPORT lean_object* lp_purelean_PureLean_InductiveCompilers_Section04_leavesFT___boxed(lean_object* v_00_u03b1_291_, lean_object* v_x_292_){
_start:
{
lean_object* v_res_293_; 
v_res_293_ = lp_purelean_PureLean_InductiveCompilers_Section04_leavesFT(v_00_u03b1_291_, v_x_292_);
lean_dec_ref(v_x_292_);
return v_res_293_;
}
}
LEAN_EXPORT lean_object* lp_purelean_PureLean_InductiveCompilers_Section04_forksFT___redArg(lean_object* v_x_294_){
_start:
{
if (lean_obj_tag(v_x_294_) == 0)
{
lean_object* v___x_295_; 
v___x_295_ = lean_unsigned_to_nat(0u);
return v___x_295_;
}
else
{
lean_object* v_a_296_; lean_object* v_a_297_; lean_object* v___x_298_; lean_object* v___x_299_; lean_object* v___x_300_; lean_object* v___x_301_; lean_object* v___x_302_; 
v_a_296_ = lean_ctor_get(v_x_294_, 0);
v_a_297_ = lean_ctor_get(v_x_294_, 1);
v___x_298_ = lean_unsigned_to_nat(1u);
v___x_299_ = lp_purelean_PureLean_InductiveCompilers_Section04_forksFT___redArg(v_a_296_);
v___x_300_ = lean_nat_add(v___x_298_, v___x_299_);
lean_dec(v___x_299_);
v___x_301_ = lp_purelean_PureLean_InductiveCompilers_Section04_forksFT___redArg(v_a_297_);
v___x_302_ = lean_nat_add(v___x_300_, v___x_301_);
lean_dec(v___x_301_);
lean_dec(v___x_300_);
return v___x_302_;
}
}
}
LEAN_EXPORT lean_object* lp_purelean_PureLean_InductiveCompilers_Section04_forksFT___redArg___boxed(lean_object* v_x_303_){
_start:
{
lean_object* v_res_304_; 
v_res_304_ = lp_purelean_PureLean_InductiveCompilers_Section04_forksFT___redArg(v_x_303_);
lean_dec_ref(v_x_303_);
return v_res_304_;
}
}
LEAN_EXPORT lean_object* lp_purelean_PureLean_InductiveCompilers_Section04_forksFT(lean_object* v_00_u03b1_305_, lean_object* v_x_306_){
_start:
{
lean_object* v___x_307_; 
v___x_307_ = lp_purelean_PureLean_InductiveCompilers_Section04_forksFT___redArg(v_x_306_);
return v___x_307_;
}
}
LEAN_EXPORT lean_object* lp_purelean_PureLean_InductiveCompilers_Section04_forksFT___boxed(lean_object* v_00_u03b1_308_, lean_object* v_x_309_){
_start:
{
lean_object* v_res_310_; 
v_res_310_ = lp_purelean_PureLean_InductiveCompilers_Section04_forksFT(v_00_u03b1_308_, v_x_309_);
lean_dec_ref(v_x_309_);
return v_res_310_;
}
}
LEAN_EXPORT lean_object* lp_purelean_PureLean_InductiveCompilers_Section04_flipFT___redArg(lean_object* v_x_311_){
_start:
{
if (lean_obj_tag(v_x_311_) == 0)
{
return v_x_311_;
}
else
{
lean_object* v_a_312_; lean_object* v_a_313_; lean_object* v___x_315_; uint8_t v_isShared_316_; uint8_t v_isSharedCheck_322_; 
v_a_312_ = lean_ctor_get(v_x_311_, 0);
v_a_313_ = lean_ctor_get(v_x_311_, 1);
v_isSharedCheck_322_ = !lean_is_exclusive(v_x_311_);
if (v_isSharedCheck_322_ == 0)
{
v___x_315_ = v_x_311_;
v_isShared_316_ = v_isSharedCheck_322_;
goto v_resetjp_314_;
}
else
{
lean_inc(v_a_313_);
lean_inc(v_a_312_);
lean_dec(v_x_311_);
v___x_315_ = lean_box(0);
v_isShared_316_ = v_isSharedCheck_322_;
goto v_resetjp_314_;
}
v_resetjp_314_:
{
lean_object* v___x_317_; lean_object* v___x_318_; lean_object* v___x_320_; 
v___x_317_ = lp_purelean_PureLean_InductiveCompilers_Section04_flipFT___redArg(v_a_313_);
v___x_318_ = lp_purelean_PureLean_InductiveCompilers_Section04_flipFT___redArg(v_a_312_);
if (v_isShared_316_ == 0)
{
lean_ctor_set(v___x_315_, 1, v___x_318_);
lean_ctor_set(v___x_315_, 0, v___x_317_);
v___x_320_ = v___x_315_;
goto v_reusejp_319_;
}
else
{
lean_object* v_reuseFailAlloc_321_; 
v_reuseFailAlloc_321_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_321_, 0, v___x_317_);
lean_ctor_set(v_reuseFailAlloc_321_, 1, v___x_318_);
v___x_320_ = v_reuseFailAlloc_321_;
goto v_reusejp_319_;
}
v_reusejp_319_:
{
return v___x_320_;
}
}
}
}
}
LEAN_EXPORT lean_object* lp_purelean_PureLean_InductiveCompilers_Section04_flipFT(lean_object* v_00_u03b1_323_, lean_object* v_x_324_){
_start:
{
lean_object* v___x_325_; 
v___x_325_ = lp_purelean_PureLean_InductiveCompilers_Section04_flipFT___redArg(v_x_324_);
return v___x_325_;
}
}
LEAN_EXPORT lean_object* lp_purelean_PureLean_InductiveCompilers_Section05_AddExpr_ctorIdx___impl(lean_object* v_x_326_){
_start:
{
lean_object* v___x_327_; 
v___x_327_ = lean_obj_tag_nat(v_x_326_);
return v___x_327_;
}
}
LEAN_EXPORT lean_object* lp_purelean_PureLean_InductiveCompilers_Section05_AddExpr_ctorIdx___impl___boxed(lean_object* v_x_328_){
_start:
{
lean_object* v_res_329_; 
v_res_329_ = lp_purelean_PureLean_InductiveCompilers_Section05_AddExpr_ctorIdx___impl(v_x_328_);
lean_dec_ref(v_x_328_);
return v_res_329_;
}
}
LEAN_EXPORT lean_object* lp_purelean_PureLean_InductiveCompilers_Section05_AddExpr_ctorElim___redArg(lean_object* v_t_330_, lean_object* v_k_331_){
_start:
{
if (lean_obj_tag(v_t_330_) == 0)
{
lean_object* v_a_332_; lean_object* v___x_333_; 
v_a_332_ = lean_ctor_get(v_t_330_, 0);
lean_inc(v_a_332_);
lean_dec_ref_known(v_t_330_, 1);
v___x_333_ = lean_apply_1(v_k_331_, v_a_332_);
return v___x_333_;
}
else
{
lean_object* v_a_334_; lean_object* v_a_335_; lean_object* v___x_336_; 
v_a_334_ = lean_ctor_get(v_t_330_, 0);
lean_inc_ref(v_a_334_);
v_a_335_ = lean_ctor_get(v_t_330_, 1);
lean_inc_ref(v_a_335_);
lean_dec_ref_known(v_t_330_, 2);
v___x_336_ = lean_apply_2(v_k_331_, v_a_334_, v_a_335_);
return v___x_336_;
}
}
}
LEAN_EXPORT lean_object* lp_purelean_PureLean_InductiveCompilers_Section05_AddExpr_ctorElim(lean_object* v_motive_337_, lean_object* v_ctorIdx_338_, lean_object* v_t_339_, lean_object* v_h_340_, lean_object* v_k_341_){
_start:
{
lean_object* v___x_342_; 
v___x_342_ = lp_purelean_PureLean_InductiveCompilers_Section05_AddExpr_ctorElim___redArg(v_t_339_, v_k_341_);
return v___x_342_;
}
}
LEAN_EXPORT lean_object* lp_purelean_PureLean_InductiveCompilers_Section05_AddExpr_ctorElim___boxed(lean_object* v_motive_343_, lean_object* v_ctorIdx_344_, lean_object* v_t_345_, lean_object* v_h_346_, lean_object* v_k_347_){
_start:
{
lean_object* v_res_348_; 
v_res_348_ = lp_purelean_PureLean_InductiveCompilers_Section05_AddExpr_ctorElim(v_motive_343_, v_ctorIdx_344_, v_t_345_, v_h_346_, v_k_347_);
lean_dec(v_ctorIdx_344_);
return v_res_348_;
}
}
LEAN_EXPORT lean_object* lp_purelean_PureLean_InductiveCompilers_Section05_AddExpr_lit_elim___redArg(lean_object* v_t_349_, lean_object* v_lit_350_){
_start:
{
lean_object* v___x_351_; 
v___x_351_ = lp_purelean_PureLean_InductiveCompilers_Section05_AddExpr_ctorElim___redArg(v_t_349_, v_lit_350_);
return v___x_351_;
}
}
LEAN_EXPORT lean_object* lp_purelean_PureLean_InductiveCompilers_Section05_AddExpr_lit_elim(lean_object* v_motive_352_, lean_object* v_t_353_, lean_object* v_h_354_, lean_object* v_lit_355_){
_start:
{
lean_object* v___x_356_; 
v___x_356_ = lp_purelean_PureLean_InductiveCompilers_Section05_AddExpr_ctorElim___redArg(v_t_353_, v_lit_355_);
return v___x_356_;
}
}
LEAN_EXPORT lean_object* lp_purelean_PureLean_InductiveCompilers_Section05_AddExpr_add_elim___redArg(lean_object* v_t_357_, lean_object* v_add_358_){
_start:
{
lean_object* v___x_359_; 
v___x_359_ = lp_purelean_PureLean_InductiveCompilers_Section05_AddExpr_ctorElim___redArg(v_t_357_, v_add_358_);
return v___x_359_;
}
}
LEAN_EXPORT lean_object* lp_purelean_PureLean_InductiveCompilers_Section05_AddExpr_add_elim(lean_object* v_motive_360_, lean_object* v_t_361_, lean_object* v_h_362_, lean_object* v_add_363_){
_start:
{
lean_object* v___x_364_; 
v___x_364_ = lp_purelean_PureLean_InductiveCompilers_Section05_AddExpr_ctorElim___redArg(v_t_361_, v_add_363_);
return v___x_364_;
}
}
LEAN_EXPORT lean_object* lp_purelean_PureLean_InductiveCompilers_Section05_evalAdd(lean_object* v_x_365_){
_start:
{
if (lean_obj_tag(v_x_365_) == 0)
{
lean_object* v_a_366_; 
v_a_366_ = lean_ctor_get(v_x_365_, 0);
lean_inc(v_a_366_);
return v_a_366_;
}
else
{
lean_object* v_a_367_; lean_object* v_a_368_; lean_object* v___x_369_; lean_object* v___x_370_; lean_object* v___x_371_; 
v_a_367_ = lean_ctor_get(v_x_365_, 0);
v_a_368_ = lean_ctor_get(v_x_365_, 1);
v___x_369_ = lp_purelean_PureLean_InductiveCompilers_Section05_evalAdd(v_a_367_);
v___x_370_ = lp_purelean_PureLean_InductiveCompilers_Section05_evalAdd(v_a_368_);
v___x_371_ = lean_nat_add(v___x_369_, v___x_370_);
lean_dec(v___x_370_);
lean_dec(v___x_369_);
return v___x_371_;
}
}
}
LEAN_EXPORT lean_object* lp_purelean_PureLean_InductiveCompilers_Section05_evalAdd___boxed(lean_object* v_x_372_){
_start:
{
lean_object* v_res_373_; 
v_res_373_ = lp_purelean_PureLean_InductiveCompilers_Section05_evalAdd(v_x_372_);
lean_dec_ref(v_x_372_);
return v_res_373_;
}
}
LEAN_EXPORT lean_object* lp_purelean_PureLean_InductiveCompilers_Section05_VMInstr_ctorIdx___impl(lean_object* v_x_374_){
_start:
{
lean_object* v___x_375_; 
v___x_375_ = lean_obj_tag_nat(v_x_374_);
return v___x_375_;
}
}
LEAN_EXPORT lean_object* lp_purelean_PureLean_InductiveCompilers_Section05_VMInstr_ctorIdx___impl___boxed(lean_object* v_x_376_){
_start:
{
lean_object* v_res_377_; 
v_res_377_ = lp_purelean_PureLean_InductiveCompilers_Section05_VMInstr_ctorIdx___impl(v_x_376_);
lean_dec(v_x_376_);
return v_res_377_;
}
}
LEAN_EXPORT lean_object* lp_purelean_PureLean_InductiveCompilers_Section05_VMInstr_ctorElim___redArg(lean_object* v_t_378_, lean_object* v_k_379_){
_start:
{
if (lean_obj_tag(v_t_378_) == 0)
{
lean_object* v_a_380_; lean_object* v___x_381_; 
v_a_380_ = lean_ctor_get(v_t_378_, 0);
lean_inc(v_a_380_);
lean_dec_ref_known(v_t_378_, 1);
v___x_381_ = lean_apply_1(v_k_379_, v_a_380_);
return v___x_381_;
}
else
{
return v_k_379_;
}
}
}
LEAN_EXPORT lean_object* lp_purelean_PureLean_InductiveCompilers_Section05_VMInstr_ctorElim(lean_object* v_motive_382_, lean_object* v_ctorIdx_383_, lean_object* v_t_384_, lean_object* v_h_385_, lean_object* v_k_386_){
_start:
{
lean_object* v___x_387_; 
v___x_387_ = lp_purelean_PureLean_InductiveCompilers_Section05_VMInstr_ctorElim___redArg(v_t_384_, v_k_386_);
return v___x_387_;
}
}
LEAN_EXPORT lean_object* lp_purelean_PureLean_InductiveCompilers_Section05_VMInstr_ctorElim___boxed(lean_object* v_motive_388_, lean_object* v_ctorIdx_389_, lean_object* v_t_390_, lean_object* v_h_391_, lean_object* v_k_392_){
_start:
{
lean_object* v_res_393_; 
v_res_393_ = lp_purelean_PureLean_InductiveCompilers_Section05_VMInstr_ctorElim(v_motive_388_, v_ctorIdx_389_, v_t_390_, v_h_391_, v_k_392_);
lean_dec(v_ctorIdx_389_);
return v_res_393_;
}
}
LEAN_EXPORT lean_object* lp_purelean_PureLean_InductiveCompilers_Section05_VMInstr_push_elim___redArg(lean_object* v_t_394_, lean_object* v_push_395_){
_start:
{
lean_object* v___x_396_; 
v___x_396_ = lp_purelean_PureLean_InductiveCompilers_Section05_VMInstr_ctorElim___redArg(v_t_394_, v_push_395_);
return v___x_396_;
}
}
LEAN_EXPORT lean_object* lp_purelean_PureLean_InductiveCompilers_Section05_VMInstr_push_elim(lean_object* v_motive_397_, lean_object* v_t_398_, lean_object* v_h_399_, lean_object* v_push_400_){
_start:
{
lean_object* v___x_401_; 
v___x_401_ = lp_purelean_PureLean_InductiveCompilers_Section05_VMInstr_ctorElim___redArg(v_t_398_, v_push_400_);
return v___x_401_;
}
}
LEAN_EXPORT lean_object* lp_purelean_PureLean_InductiveCompilers_Section05_VMInstr_addTop_elim___redArg(lean_object* v_t_402_, lean_object* v_addTop_403_){
_start:
{
lean_object* v___x_404_; 
v___x_404_ = lp_purelean_PureLean_InductiveCompilers_Section05_VMInstr_ctorElim___redArg(v_t_402_, v_addTop_403_);
return v___x_404_;
}
}
LEAN_EXPORT lean_object* lp_purelean_PureLean_InductiveCompilers_Section05_VMInstr_addTop_elim(lean_object* v_motive_405_, lean_object* v_t_406_, lean_object* v_h_407_, lean_object* v_addTop_408_){
_start:
{
lean_object* v___x_409_; 
v___x_409_ = lp_purelean_PureLean_InductiveCompilers_Section05_VMInstr_ctorElim___redArg(v_t_406_, v_addTop_408_);
return v___x_409_;
}
}
LEAN_EXPORT lean_object* lp_purelean_PureLean_InductiveCompilers_Section05_runVM(lean_object* v_x_410_, lean_object* v_x_411_){
_start:
{
if (lean_obj_tag(v_x_410_) == 0)
{
return v_x_411_;
}
else
{
lean_object* v_head_412_; 
v_head_412_ = lean_ctor_get(v_x_410_, 0);
if (lean_obj_tag(v_head_412_) == 0)
{
lean_object* v_tail_413_; lean_object* v___x_415_; uint8_t v_isShared_416_; uint8_t v_isSharedCheck_422_; 
lean_inc_ref(v_head_412_);
v_tail_413_ = lean_ctor_get(v_x_410_, 1);
v_isSharedCheck_422_ = !lean_is_exclusive(v_x_410_);
if (v_isSharedCheck_422_ == 0)
{
lean_object* v_unused_423_; 
v_unused_423_ = lean_ctor_get(v_x_410_, 0);
lean_dec(v_unused_423_);
v___x_415_ = v_x_410_;
v_isShared_416_ = v_isSharedCheck_422_;
goto v_resetjp_414_;
}
else
{
lean_inc(v_tail_413_);
lean_dec(v_x_410_);
v___x_415_ = lean_box(0);
v_isShared_416_ = v_isSharedCheck_422_;
goto v_resetjp_414_;
}
v_resetjp_414_:
{
lean_object* v_a_417_; lean_object* v___x_419_; 
v_a_417_ = lean_ctor_get(v_head_412_, 0);
lean_inc(v_a_417_);
lean_dec_ref_known(v_head_412_, 1);
if (v_isShared_416_ == 0)
{
lean_ctor_set(v___x_415_, 1, v_x_411_);
lean_ctor_set(v___x_415_, 0, v_a_417_);
v___x_419_ = v___x_415_;
goto v_reusejp_418_;
}
else
{
lean_object* v_reuseFailAlloc_421_; 
v_reuseFailAlloc_421_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_421_, 0, v_a_417_);
lean_ctor_set(v_reuseFailAlloc_421_, 1, v_x_411_);
v___x_419_ = v_reuseFailAlloc_421_;
goto v_reusejp_418_;
}
v_reusejp_418_:
{
v_x_410_ = v_tail_413_;
v_x_411_ = v___x_419_;
goto _start;
}
}
}
else
{
if (lean_obj_tag(v_x_411_) == 1)
{
lean_object* v_tail_424_; 
v_tail_424_ = lean_ctor_get(v_x_411_, 1);
lean_inc(v_tail_424_);
if (lean_obj_tag(v_tail_424_) == 1)
{
lean_object* v_tail_425_; lean_object* v_head_426_; lean_object* v_head_427_; lean_object* v_tail_428_; lean_object* v___x_430_; uint8_t v_isShared_431_; uint8_t v_isSharedCheck_437_; 
v_tail_425_ = lean_ctor_get(v_x_410_, 1);
lean_inc(v_tail_425_);
lean_dec_ref_known(v_x_410_, 2);
v_head_426_ = lean_ctor_get(v_x_411_, 0);
lean_inc(v_head_426_);
lean_dec_ref_known(v_x_411_, 2);
v_head_427_ = lean_ctor_get(v_tail_424_, 0);
v_tail_428_ = lean_ctor_get(v_tail_424_, 1);
v_isSharedCheck_437_ = !lean_is_exclusive(v_tail_424_);
if (v_isSharedCheck_437_ == 0)
{
v___x_430_ = v_tail_424_;
v_isShared_431_ = v_isSharedCheck_437_;
goto v_resetjp_429_;
}
else
{
lean_inc(v_tail_428_);
lean_inc(v_head_427_);
lean_dec(v_tail_424_);
v___x_430_ = lean_box(0);
v_isShared_431_ = v_isSharedCheck_437_;
goto v_resetjp_429_;
}
v_resetjp_429_:
{
lean_object* v___x_432_; lean_object* v___x_434_; 
v___x_432_ = lean_nat_add(v_head_427_, v_head_426_);
lean_dec(v_head_426_);
lean_dec(v_head_427_);
if (v_isShared_431_ == 0)
{
lean_ctor_set(v___x_430_, 0, v___x_432_);
v___x_434_ = v___x_430_;
goto v_reusejp_433_;
}
else
{
lean_object* v_reuseFailAlloc_436_; 
v_reuseFailAlloc_436_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_436_, 0, v___x_432_);
lean_ctor_set(v_reuseFailAlloc_436_, 1, v_tail_428_);
v___x_434_ = v_reuseFailAlloc_436_;
goto v_reusejp_433_;
}
v_reusejp_433_:
{
v_x_410_ = v_tail_425_;
v_x_411_ = v___x_434_;
goto _start;
}
}
}
else
{
lean_object* v_tail_438_; 
lean_dec(v_tail_424_);
v_tail_438_ = lean_ctor_get(v_x_410_, 1);
lean_inc(v_tail_438_);
lean_dec_ref_known(v_x_410_, 2);
v_x_410_ = v_tail_438_;
goto _start;
}
}
else
{
lean_object* v_tail_440_; 
v_tail_440_ = lean_ctor_get(v_x_410_, 1);
lean_inc(v_tail_440_);
lean_dec_ref_known(v_x_410_, 2);
v_x_410_ = v_tail_440_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* lp_purelean_PureLean_InductiveCompilers_Section05_compileAdd(lean_object* v_x_445_){
_start:
{
if (lean_obj_tag(v_x_445_) == 0)
{
lean_object* v_a_446_; lean_object* v___x_448_; uint8_t v_isShared_449_; uint8_t v_isSharedCheck_455_; 
v_a_446_ = lean_ctor_get(v_x_445_, 0);
v_isSharedCheck_455_ = !lean_is_exclusive(v_x_445_);
if (v_isSharedCheck_455_ == 0)
{
v___x_448_ = v_x_445_;
v_isShared_449_ = v_isSharedCheck_455_;
goto v_resetjp_447_;
}
else
{
lean_inc(v_a_446_);
lean_dec(v_x_445_);
v___x_448_ = lean_box(0);
v_isShared_449_ = v_isSharedCheck_455_;
goto v_resetjp_447_;
}
v_resetjp_447_:
{
lean_object* v___x_451_; 
if (v_isShared_449_ == 0)
{
v___x_451_ = v___x_448_;
goto v_reusejp_450_;
}
else
{
lean_object* v_reuseFailAlloc_454_; 
v_reuseFailAlloc_454_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_454_, 0, v_a_446_);
v___x_451_ = v_reuseFailAlloc_454_;
goto v_reusejp_450_;
}
v_reusejp_450_:
{
lean_object* v___x_452_; lean_object* v___x_453_; 
v___x_452_ = lean_box(0);
v___x_453_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_453_, 0, v___x_451_);
lean_ctor_set(v___x_453_, 1, v___x_452_);
return v___x_453_;
}
}
}
else
{
lean_object* v_a_456_; lean_object* v_a_457_; lean_object* v___x_458_; lean_object* v___x_459_; lean_object* v___x_460_; lean_object* v___x_461_; lean_object* v___x_462_; 
v_a_456_ = lean_ctor_get(v_x_445_, 0);
lean_inc_ref(v_a_456_);
v_a_457_ = lean_ctor_get(v_x_445_, 1);
lean_inc_ref(v_a_457_);
lean_dec_ref_known(v_x_445_, 2);
v___x_458_ = lp_purelean_PureLean_InductiveCompilers_Section05_compileAdd(v_a_456_);
v___x_459_ = lp_purelean_PureLean_InductiveCompilers_Section05_compileAdd(v_a_457_);
v___x_460_ = l_List_appendTR___redArg(v___x_458_, v___x_459_);
v___x_461_ = ((lean_object*)(lp_purelean_PureLean_InductiveCompilers_Section05_compileAdd___closed__0));
v___x_462_ = l_List_appendTR___redArg(v___x_460_, v___x_461_);
return v___x_462_;
}
}
}
LEAN_EXPORT lean_object* lp_purelean_PureLean_InductiveCompilers_Section06_PureExpr_ctorIdx___impl(lean_object* v_x_463_){
_start:
{
lean_object* v___x_464_; 
v___x_464_ = lean_obj_tag_nat(v_x_463_);
return v___x_464_;
}
}
LEAN_EXPORT lean_object* lp_purelean_PureLean_InductiveCompilers_Section06_PureExpr_ctorIdx___impl___boxed(lean_object* v_x_465_){
_start:
{
lean_object* v_res_466_; 
v_res_466_ = lp_purelean_PureLean_InductiveCompilers_Section06_PureExpr_ctorIdx___impl(v_x_465_);
lean_dec_ref(v_x_465_);
return v_res_466_;
}
}
LEAN_EXPORT lean_object* lp_purelean_PureLean_InductiveCompilers_Section06_PureExpr_ctorElim___redArg(lean_object* v_t_467_, lean_object* v_k_468_){
_start:
{
switch(lean_obj_tag(v_t_467_))
{
case 2:
{
lean_object* v_a_469_; lean_object* v_a_470_; lean_object* v___x_471_; 
v_a_469_ = lean_ctor_get(v_t_467_, 0);
lean_inc_ref(v_a_469_);
v_a_470_ = lean_ctor_get(v_t_467_, 1);
lean_inc_ref(v_a_470_);
lean_dec_ref_known(v_t_467_, 2);
v___x_471_ = lean_apply_2(v_k_468_, v_a_469_, v_a_470_);
return v___x_471_;
}
case 3:
{
lean_object* v_a_472_; lean_object* v_a_473_; lean_object* v___x_474_; 
v_a_472_ = lean_ctor_get(v_t_467_, 0);
lean_inc_ref(v_a_472_);
v_a_473_ = lean_ctor_get(v_t_467_, 1);
lean_inc_ref(v_a_473_);
lean_dec_ref_known(v_t_467_, 2);
v___x_474_ = lean_apply_2(v_k_468_, v_a_472_, v_a_473_);
return v___x_474_;
}
default: 
{
lean_object* v_a_475_; lean_object* v___x_476_; 
v_a_475_ = lean_ctor_get(v_t_467_, 0);
lean_inc(v_a_475_);
lean_dec_ref(v_t_467_);
v___x_476_ = lean_apply_1(v_k_468_, v_a_475_);
return v___x_476_;
}
}
}
}
LEAN_EXPORT lean_object* lp_purelean_PureLean_InductiveCompilers_Section06_PureExpr_ctorElim(lean_object* v_motive_477_, lean_object* v_ctorIdx_478_, lean_object* v_t_479_, lean_object* v_h_480_, lean_object* v_k_481_){
_start:
{
lean_object* v___x_482_; 
v___x_482_ = lp_purelean_PureLean_InductiveCompilers_Section06_PureExpr_ctorElim___redArg(v_t_479_, v_k_481_);
return v___x_482_;
}
}
LEAN_EXPORT lean_object* lp_purelean_PureLean_InductiveCompilers_Section06_PureExpr_ctorElim___boxed(lean_object* v_motive_483_, lean_object* v_ctorIdx_484_, lean_object* v_t_485_, lean_object* v_h_486_, lean_object* v_k_487_){
_start:
{
lean_object* v_res_488_; 
v_res_488_ = lp_purelean_PureLean_InductiveCompilers_Section06_PureExpr_ctorElim(v_motive_483_, v_ctorIdx_484_, v_t_485_, v_h_486_, v_k_487_);
lean_dec(v_ctorIdx_484_);
return v_res_488_;
}
}
LEAN_EXPORT lean_object* lp_purelean_PureLean_InductiveCompilers_Section06_PureExpr_lit_elim___redArg(lean_object* v_t_489_, lean_object* v_lit_490_){
_start:
{
lean_object* v___x_491_; 
v___x_491_ = lp_purelean_PureLean_InductiveCompilers_Section06_PureExpr_ctorElim___redArg(v_t_489_, v_lit_490_);
return v___x_491_;
}
}
LEAN_EXPORT lean_object* lp_purelean_PureLean_InductiveCompilers_Section06_PureExpr_lit_elim(lean_object* v_motive_492_, lean_object* v_t_493_, lean_object* v_h_494_, lean_object* v_lit_495_){
_start:
{
lean_object* v___x_496_; 
v___x_496_ = lp_purelean_PureLean_InductiveCompilers_Section06_PureExpr_ctorElim___redArg(v_t_493_, v_lit_495_);
return v___x_496_;
}
}
LEAN_EXPORT lean_object* lp_purelean_PureLean_InductiveCompilers_Section06_PureExpr_var_elim___redArg(lean_object* v_t_497_, lean_object* v_var_498_){
_start:
{
lean_object* v___x_499_; 
v___x_499_ = lp_purelean_PureLean_InductiveCompilers_Section06_PureExpr_ctorElim___redArg(v_t_497_, v_var_498_);
return v___x_499_;
}
}
LEAN_EXPORT lean_object* lp_purelean_PureLean_InductiveCompilers_Section06_PureExpr_var_elim(lean_object* v_motive_500_, lean_object* v_t_501_, lean_object* v_h_502_, lean_object* v_var_503_){
_start:
{
lean_object* v___x_504_; 
v___x_504_ = lp_purelean_PureLean_InductiveCompilers_Section06_PureExpr_ctorElim___redArg(v_t_501_, v_var_503_);
return v___x_504_;
}
}
LEAN_EXPORT lean_object* lp_purelean_PureLean_InductiveCompilers_Section06_PureExpr_add_elim___redArg(lean_object* v_t_505_, lean_object* v_add_506_){
_start:
{
lean_object* v___x_507_; 
v___x_507_ = lp_purelean_PureLean_InductiveCompilers_Section06_PureExpr_ctorElim___redArg(v_t_505_, v_add_506_);
return v___x_507_;
}
}
LEAN_EXPORT lean_object* lp_purelean_PureLean_InductiveCompilers_Section06_PureExpr_add_elim(lean_object* v_motive_508_, lean_object* v_t_509_, lean_object* v_h_510_, lean_object* v_add_511_){
_start:
{
lean_object* v___x_512_; 
v___x_512_ = lp_purelean_PureLean_InductiveCompilers_Section06_PureExpr_ctorElim___redArg(v_t_509_, v_add_511_);
return v___x_512_;
}
}
LEAN_EXPORT lean_object* lp_purelean_PureLean_InductiveCompilers_Section06_PureExpr_mul_elim___redArg(lean_object* v_t_513_, lean_object* v_mul_514_){
_start:
{
lean_object* v___x_515_; 
v___x_515_ = lp_purelean_PureLean_InductiveCompilers_Section06_PureExpr_ctorElim___redArg(v_t_513_, v_mul_514_);
return v___x_515_;
}
}
LEAN_EXPORT lean_object* lp_purelean_PureLean_InductiveCompilers_Section06_PureExpr_mul_elim(lean_object* v_motive_516_, lean_object* v_t_517_, lean_object* v_h_518_, lean_object* v_mul_519_){
_start:
{
lean_object* v___x_520_; 
v___x_520_ = lp_purelean_PureLean_InductiveCompilers_Section06_PureExpr_ctorElim___redArg(v_t_517_, v_mul_519_);
return v___x_520_;
}
}
LEAN_EXPORT lean_object* lp_purelean_PureLean_InductiveCompilers_Section06_evalExpr(lean_object* v_env_521_, lean_object* v_x_522_){
_start:
{
switch(lean_obj_tag(v_x_522_))
{
case 0:
{
lean_object* v_a_523_; 
lean_dec_ref(v_env_521_);
v_a_523_ = lean_ctor_get(v_x_522_, 0);
lean_inc(v_a_523_);
lean_dec_ref_known(v_x_522_, 1);
return v_a_523_;
}
case 1:
{
lean_object* v_a_524_; lean_object* v___x_525_; 
v_a_524_ = lean_ctor_get(v_x_522_, 0);
lean_inc(v_a_524_);
lean_dec_ref_known(v_x_522_, 1);
v___x_525_ = lean_apply_1(v_env_521_, v_a_524_);
return v___x_525_;
}
case 2:
{
lean_object* v_a_526_; lean_object* v_a_527_; lean_object* v___x_528_; lean_object* v___x_529_; lean_object* v___x_530_; 
v_a_526_ = lean_ctor_get(v_x_522_, 0);
lean_inc_ref(v_a_526_);
v_a_527_ = lean_ctor_get(v_x_522_, 1);
lean_inc_ref(v_a_527_);
lean_dec_ref_known(v_x_522_, 2);
lean_inc_ref(v_env_521_);
v___x_528_ = lp_purelean_PureLean_InductiveCompilers_Section06_evalExpr(v_env_521_, v_a_526_);
v___x_529_ = lp_purelean_PureLean_InductiveCompilers_Section06_evalExpr(v_env_521_, v_a_527_);
v___x_530_ = lean_nat_add(v___x_528_, v___x_529_);
lean_dec(v___x_529_);
lean_dec(v___x_528_);
return v___x_530_;
}
default: 
{
lean_object* v_a_531_; lean_object* v_a_532_; lean_object* v___x_533_; lean_object* v___x_534_; lean_object* v___x_535_; 
v_a_531_ = lean_ctor_get(v_x_522_, 0);
lean_inc_ref(v_a_531_);
v_a_532_ = lean_ctor_get(v_x_522_, 1);
lean_inc_ref(v_a_532_);
lean_dec_ref_known(v_x_522_, 2);
lean_inc_ref(v_env_521_);
v___x_533_ = lp_purelean_PureLean_InductiveCompilers_Section06_evalExpr(v_env_521_, v_a_531_);
v___x_534_ = lp_purelean_PureLean_InductiveCompilers_Section06_evalExpr(v_env_521_, v_a_532_);
v___x_535_ = lean_nat_mul(v___x_533_, v___x_534_);
lean_dec(v___x_534_);
lean_dec(v___x_533_);
return v___x_535_;
}
}
}
}
LEAN_EXPORT lean_object* lp_purelean_PureLean_InductiveCompilers_Section06_swapAddExpr(lean_object* v_x_536_){
_start:
{
switch(lean_obj_tag(v_x_536_))
{
case 2:
{
lean_object* v_a_537_; lean_object* v_a_538_; lean_object* v___x_540_; uint8_t v_isShared_541_; uint8_t v_isSharedCheck_547_; 
v_a_537_ = lean_ctor_get(v_x_536_, 0);
v_a_538_ = lean_ctor_get(v_x_536_, 1);
v_isSharedCheck_547_ = !lean_is_exclusive(v_x_536_);
if (v_isSharedCheck_547_ == 0)
{
v___x_540_ = v_x_536_;
v_isShared_541_ = v_isSharedCheck_547_;
goto v_resetjp_539_;
}
else
{
lean_inc(v_a_538_);
lean_inc(v_a_537_);
lean_dec(v_x_536_);
v___x_540_ = lean_box(0);
v_isShared_541_ = v_isSharedCheck_547_;
goto v_resetjp_539_;
}
v_resetjp_539_:
{
lean_object* v___x_542_; lean_object* v___x_543_; lean_object* v___x_545_; 
v___x_542_ = lp_purelean_PureLean_InductiveCompilers_Section06_swapAddExpr(v_a_538_);
v___x_543_ = lp_purelean_PureLean_InductiveCompilers_Section06_swapAddExpr(v_a_537_);
if (v_isShared_541_ == 0)
{
lean_ctor_set(v___x_540_, 1, v___x_543_);
lean_ctor_set(v___x_540_, 0, v___x_542_);
v___x_545_ = v___x_540_;
goto v_reusejp_544_;
}
else
{
lean_object* v_reuseFailAlloc_546_; 
v_reuseFailAlloc_546_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_546_, 0, v___x_542_);
lean_ctor_set(v_reuseFailAlloc_546_, 1, v___x_543_);
v___x_545_ = v_reuseFailAlloc_546_;
goto v_reusejp_544_;
}
v_reusejp_544_:
{
return v___x_545_;
}
}
}
case 3:
{
lean_object* v_a_548_; lean_object* v_a_549_; lean_object* v___x_551_; uint8_t v_isShared_552_; uint8_t v_isSharedCheck_558_; 
v_a_548_ = lean_ctor_get(v_x_536_, 0);
v_a_549_ = lean_ctor_get(v_x_536_, 1);
v_isSharedCheck_558_ = !lean_is_exclusive(v_x_536_);
if (v_isSharedCheck_558_ == 0)
{
v___x_551_ = v_x_536_;
v_isShared_552_ = v_isSharedCheck_558_;
goto v_resetjp_550_;
}
else
{
lean_inc(v_a_549_);
lean_inc(v_a_548_);
lean_dec(v_x_536_);
v___x_551_ = lean_box(0);
v_isShared_552_ = v_isSharedCheck_558_;
goto v_resetjp_550_;
}
v_resetjp_550_:
{
lean_object* v___x_553_; lean_object* v___x_554_; lean_object* v___x_556_; 
v___x_553_ = lp_purelean_PureLean_InductiveCompilers_Section06_swapAddExpr(v_a_548_);
v___x_554_ = lp_purelean_PureLean_InductiveCompilers_Section06_swapAddExpr(v_a_549_);
if (v_isShared_552_ == 0)
{
lean_ctor_set(v___x_551_, 1, v___x_554_);
lean_ctor_set(v___x_551_, 0, v___x_553_);
v___x_556_ = v___x_551_;
goto v_reusejp_555_;
}
else
{
lean_object* v_reuseFailAlloc_557_; 
v_reuseFailAlloc_557_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_reuseFailAlloc_557_, 0, v___x_553_);
lean_ctor_set(v_reuseFailAlloc_557_, 1, v___x_554_);
v___x_556_ = v_reuseFailAlloc_557_;
goto v_reusejp_555_;
}
v_reusejp_555_:
{
return v___x_556_;
}
}
}
default: 
{
return v_x_536_;
}
}
}
}
LEAN_EXPORT lean_object* lp_purelean_PureLean_InductiveCompilers_Section06_optZeroExpr(lean_object* v_x_559_){
_start:
{
switch(lean_obj_tag(v_x_559_))
{
case 2:
{
lean_object* v_a_560_; lean_object* v_a_561_; lean_object* v___x_563_; uint8_t v_isShared_564_; uint8_t v_isSharedCheck_589_; 
v_a_560_ = lean_ctor_get(v_x_559_, 0);
v_a_561_ = lean_ctor_get(v_x_559_, 1);
v_isSharedCheck_589_ = !lean_is_exclusive(v_x_559_);
if (v_isSharedCheck_589_ == 0)
{
v___x_563_ = v_x_559_;
v_isShared_564_ = v_isSharedCheck_589_;
goto v_resetjp_562_;
}
else
{
lean_inc(v_a_561_);
lean_inc(v_a_560_);
lean_dec(v_x_559_);
v___x_563_ = lean_box(0);
v_isShared_564_ = v_isSharedCheck_589_;
goto v_resetjp_562_;
}
v_resetjp_562_:
{
lean_object* v___x_565_; 
v___x_565_ = lp_purelean_PureLean_InductiveCompilers_Section06_optZeroExpr(v_a_560_);
if (lean_obj_tag(v___x_565_) == 0)
{
lean_object* v_a_566_; lean_object* v___x_567_; uint8_t v___x_568_; 
v_a_566_ = lean_ctor_get(v___x_565_, 0);
v___x_567_ = lean_unsigned_to_nat(0u);
v___x_568_ = lean_nat_dec_eq(v_a_566_, v___x_567_);
if (v___x_568_ == 0)
{
lean_object* v___x_569_; 
v___x_569_ = lp_purelean_PureLean_InductiveCompilers_Section06_optZeroExpr(v_a_561_);
if (lean_obj_tag(v___x_569_) == 0)
{
lean_object* v_a_570_; uint8_t v___x_571_; 
v_a_570_ = lean_ctor_get(v___x_569_, 0);
v___x_571_ = lean_nat_dec_eq(v_a_570_, v___x_567_);
if (v___x_571_ == 0)
{
lean_object* v___x_573_; 
if (v_isShared_564_ == 0)
{
lean_ctor_set(v___x_563_, 1, v___x_569_);
lean_ctor_set(v___x_563_, 0, v___x_565_);
v___x_573_ = v___x_563_;
goto v_reusejp_572_;
}
else
{
lean_object* v_reuseFailAlloc_574_; 
v_reuseFailAlloc_574_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_574_, 0, v___x_565_);
lean_ctor_set(v_reuseFailAlloc_574_, 1, v___x_569_);
v___x_573_ = v_reuseFailAlloc_574_;
goto v_reusejp_572_;
}
v_reusejp_572_:
{
return v___x_573_;
}
}
else
{
lean_dec_ref_known(v___x_569_, 1);
lean_del_object(v___x_563_);
return v___x_565_;
}
}
else
{
lean_object* v___x_576_; 
if (v_isShared_564_ == 0)
{
lean_ctor_set(v___x_563_, 1, v___x_569_);
lean_ctor_set(v___x_563_, 0, v___x_565_);
v___x_576_ = v___x_563_;
goto v_reusejp_575_;
}
else
{
lean_object* v_reuseFailAlloc_577_; 
v_reuseFailAlloc_577_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_577_, 0, v___x_565_);
lean_ctor_set(v_reuseFailAlloc_577_, 1, v___x_569_);
v___x_576_ = v_reuseFailAlloc_577_;
goto v_reusejp_575_;
}
v_reusejp_575_:
{
return v___x_576_;
}
}
}
else
{
lean_dec_ref_known(v___x_565_, 1);
lean_del_object(v___x_563_);
v_x_559_ = v_a_561_;
goto _start;
}
}
else
{
lean_object* v___x_579_; 
v___x_579_ = lp_purelean_PureLean_InductiveCompilers_Section06_optZeroExpr(v_a_561_);
if (lean_obj_tag(v___x_579_) == 0)
{
lean_object* v_a_580_; lean_object* v___x_581_; uint8_t v___x_582_; 
v_a_580_ = lean_ctor_get(v___x_579_, 0);
v___x_581_ = lean_unsigned_to_nat(0u);
v___x_582_ = lean_nat_dec_eq(v_a_580_, v___x_581_);
if (v___x_582_ == 0)
{
lean_object* v___x_584_; 
if (v_isShared_564_ == 0)
{
lean_ctor_set(v___x_563_, 1, v___x_579_);
lean_ctor_set(v___x_563_, 0, v___x_565_);
v___x_584_ = v___x_563_;
goto v_reusejp_583_;
}
else
{
lean_object* v_reuseFailAlloc_585_; 
v_reuseFailAlloc_585_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_585_, 0, v___x_565_);
lean_ctor_set(v_reuseFailAlloc_585_, 1, v___x_579_);
v___x_584_ = v_reuseFailAlloc_585_;
goto v_reusejp_583_;
}
v_reusejp_583_:
{
return v___x_584_;
}
}
else
{
lean_dec_ref_known(v___x_579_, 1);
lean_del_object(v___x_563_);
return v___x_565_;
}
}
else
{
lean_object* v___x_587_; 
if (v_isShared_564_ == 0)
{
lean_ctor_set(v___x_563_, 1, v___x_579_);
lean_ctor_set(v___x_563_, 0, v___x_565_);
v___x_587_ = v___x_563_;
goto v_reusejp_586_;
}
else
{
lean_object* v_reuseFailAlloc_588_; 
v_reuseFailAlloc_588_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_588_, 0, v___x_565_);
lean_ctor_set(v_reuseFailAlloc_588_, 1, v___x_579_);
v___x_587_ = v_reuseFailAlloc_588_;
goto v_reusejp_586_;
}
v_reusejp_586_:
{
return v___x_587_;
}
}
}
}
}
case 3:
{
lean_object* v_a_590_; lean_object* v_a_591_; lean_object* v___x_593_; uint8_t v_isShared_594_; uint8_t v_isSharedCheck_600_; 
v_a_590_ = lean_ctor_get(v_x_559_, 0);
v_a_591_ = lean_ctor_get(v_x_559_, 1);
v_isSharedCheck_600_ = !lean_is_exclusive(v_x_559_);
if (v_isSharedCheck_600_ == 0)
{
v___x_593_ = v_x_559_;
v_isShared_594_ = v_isSharedCheck_600_;
goto v_resetjp_592_;
}
else
{
lean_inc(v_a_591_);
lean_inc(v_a_590_);
lean_dec(v_x_559_);
v___x_593_ = lean_box(0);
v_isShared_594_ = v_isSharedCheck_600_;
goto v_resetjp_592_;
}
v_resetjp_592_:
{
lean_object* v___x_595_; lean_object* v___x_596_; lean_object* v___x_598_; 
v___x_595_ = lp_purelean_PureLean_InductiveCompilers_Section06_optZeroExpr(v_a_590_);
v___x_596_ = lp_purelean_PureLean_InductiveCompilers_Section06_optZeroExpr(v_a_591_);
if (v_isShared_594_ == 0)
{
lean_ctor_set(v___x_593_, 1, v___x_596_);
lean_ctor_set(v___x_593_, 0, v___x_595_);
v___x_598_ = v___x_593_;
goto v_reusejp_597_;
}
else
{
lean_object* v_reuseFailAlloc_599_; 
v_reuseFailAlloc_599_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_reuseFailAlloc_599_, 0, v___x_595_);
lean_ctor_set(v_reuseFailAlloc_599_, 1, v___x_596_);
v___x_598_ = v_reuseFailAlloc_599_;
goto v_reusejp_597_;
}
v_reusejp_597_:
{
return v___x_598_;
}
}
}
default: 
{
return v_x_559_;
}
}
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_purelean_PureLean_InductiveCompilers(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
lean_initialize_runtime_module();
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
