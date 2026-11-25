// Lean compiler output
// Module: PureLean.HardBenchmarks
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
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_List_appendTR___redArg(lean_object*, lean_object*);
lean_object* lean_obj_tag_nat(lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_purelean_hq__04__btree__flatten__mirror_BTree_ctorIdx___impl___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_purelean_hq__04__btree__flatten__mirror_BTree_ctorIdx___impl___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_purelean_hq__04__btree__flatten__mirror_BTree_ctorIdx___impl(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_purelean_hq__04__btree__flatten__mirror_BTree_ctorIdx___impl___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_purelean_hq__04__btree__flatten__mirror_BTree_ctorElim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_purelean_hq__04__btree__flatten__mirror_BTree_ctorElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_purelean_hq__04__btree__flatten__mirror_BTree_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_purelean_hq__04__btree__flatten__mirror_BTree_leaf_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_purelean_hq__04__btree__flatten__mirror_BTree_leaf_elim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_purelean_hq__04__btree__flatten__mirror_BTree_node_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_purelean_hq__04__btree__flatten__mirror_BTree_node_elim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_purelean_hq__04__btree__flatten__mirror_mirrorT___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_purelean_hq__04__btree__flatten__mirror_mirrorT(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_purelean_hq__04__btree__flatten__mirror_flattenBT___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_purelean_hq__04__btree__flatten__mirror_flattenBT___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_purelean_hq__04__btree__flatten__mirror_flattenBT(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_purelean_hq__04__btree__flatten__mirror_flattenBT___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_purelean_hq__06__mapAcc__correct_mapAcc___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_purelean_hq__06__mapAcc__correct_mapAcc(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_purelean_hq__11__foldl__via__foldr__cps_foldrL___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_purelean_hq__11__foldl__via__foldr__cps_foldrL___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_purelean_hq__11__foldl__via__foldr__cps_foldrL(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_purelean_hq__11__foldl__via__foldr__cps_foldrL___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_purelean_hq__11__foldl__via__foldr__cps_foldlL___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_purelean_hq__11__foldl__via__foldr__cps_foldlL(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_purelean_hq__12__group__commutator__inv_commG___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_purelean_hq__12__group__commutator__inv_commG(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_purelean_hq__13__fib__addition__formula_fibN(lean_object*);
LEAN_EXPORT lean_object* lp_purelean_hq__13__fib__addition__formula_fibN___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_purelean_hq__14__arith__vm__compiler_ArithAST_ctorIdx___impl(lean_object*);
LEAN_EXPORT lean_object* lp_purelean_hq__14__arith__vm__compiler_ArithAST_ctorIdx___impl___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_purelean_hq__14__arith__vm__compiler_ArithAST_ctorElim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_purelean_hq__14__arith__vm__compiler_ArithAST_ctorElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_purelean_hq__14__arith__vm__compiler_ArithAST_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_purelean_hq__14__arith__vm__compiler_ArithAST_lit_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_purelean_hq__14__arith__vm__compiler_ArithAST_lit_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_purelean_hq__14__arith__vm__compiler_ArithAST_add_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_purelean_hq__14__arith__vm__compiler_ArithAST_add_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_purelean_hq__14__arith__vm__compiler_ArithAST_mul_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_purelean_hq__14__arith__vm__compiler_ArithAST_mul_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_purelean_hq__14__arith__vm__compiler_evalAST(lean_object*);
LEAN_EXPORT lean_object* lp_purelean_hq__14__arith__vm__compiler_evalAST___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_purelean_hq__14__arith__vm__compiler_OpInstr_ctorIdx___impl(lean_object*);
LEAN_EXPORT lean_object* lp_purelean_hq__14__arith__vm__compiler_OpInstr_ctorIdx___impl___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_purelean_hq__14__arith__vm__compiler_OpInstr_ctorElim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_purelean_hq__14__arith__vm__compiler_OpInstr_ctorElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_purelean_hq__14__arith__vm__compiler_OpInstr_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_purelean_hq__14__arith__vm__compiler_OpInstr_push_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_purelean_hq__14__arith__vm__compiler_OpInstr_push_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_purelean_hq__14__arith__vm__compiler_OpInstr_addOp_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_purelean_hq__14__arith__vm__compiler_OpInstr_addOp_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_purelean_hq__14__arith__vm__compiler_OpInstr_mulOp_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_purelean_hq__14__arith__vm__compiler_OpInstr_mulOp_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_purelean_hq__14__arith__vm__compiler_execOps(lean_object*, lean_object*);
static const lean_ctor_object lp_purelean_hq__14__arith__vm__compiler_compileAST___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(1) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* lp_purelean_hq__14__arith__vm__compiler_compileAST___closed__0 = (const lean_object*)&lp_purelean_hq__14__arith__vm__compiler_compileAST___closed__0_value;
static const lean_ctor_object lp_purelean_hq__14__arith__vm__compiler_compileAST___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(2) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* lp_purelean_hq__14__arith__vm__compiler_compileAST___closed__1 = (const lean_object*)&lp_purelean_hq__14__arith__vm__compiler_compileAST___closed__1_value;
LEAN_EXPORT lean_object* lp_purelean_hq__14__arith__vm__compiler_compileAST(lean_object*);
LEAN_EXPORT lean_object* lp_purelean_hq__15__nicomachus__sum__cubes_sumCubes(lean_object*);
LEAN_EXPORT lean_object* lp_purelean_hq__15__nicomachus__sum__cubes_sumCubes___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_purelean_hq__04__btree__flatten__mirror_BTree_ctorIdx___impl___redArg(lean_object* v_x_1_){
_start:
{
lean_object* v___x_2_; 
v___x_2_ = lean_obj_tag_nat(v_x_1_);
return v___x_2_;
}
}
LEAN_EXPORT lean_object* lp_purelean_hq__04__btree__flatten__mirror_BTree_ctorIdx___impl___redArg___boxed(lean_object* v_x_3_){
_start:
{
lean_object* v_res_4_; 
v_res_4_ = lp_purelean_hq__04__btree__flatten__mirror_BTree_ctorIdx___impl___redArg(v_x_3_);
lean_dec(v_x_3_);
return v_res_4_;
}
}
LEAN_EXPORT lean_object* lp_purelean_hq__04__btree__flatten__mirror_BTree_ctorIdx___impl(lean_object* v_00_u03b1_5_, lean_object* v_x_6_){
_start:
{
lean_object* v___x_7_; 
v___x_7_ = lean_obj_tag_nat(v_x_6_);
return v___x_7_;
}
}
LEAN_EXPORT lean_object* lp_purelean_hq__04__btree__flatten__mirror_BTree_ctorIdx___impl___boxed(lean_object* v_00_u03b1_8_, lean_object* v_x_9_){
_start:
{
lean_object* v_res_10_; 
v_res_10_ = lp_purelean_hq__04__btree__flatten__mirror_BTree_ctorIdx___impl(v_00_u03b1_8_, v_x_9_);
lean_dec(v_x_9_);
return v_res_10_;
}
}
LEAN_EXPORT lean_object* lp_purelean_hq__04__btree__flatten__mirror_BTree_ctorElim___redArg(lean_object* v_t_11_, lean_object* v_k_12_){
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
LEAN_EXPORT lean_object* lp_purelean_hq__04__btree__flatten__mirror_BTree_ctorElim(lean_object* v_00_u03b1_17_, lean_object* v_motive_18_, lean_object* v_ctorIdx_19_, lean_object* v_t_20_, lean_object* v_h_21_, lean_object* v_k_22_){
_start:
{
lean_object* v___x_23_; 
v___x_23_ = lp_purelean_hq__04__btree__flatten__mirror_BTree_ctorElim___redArg(v_t_20_, v_k_22_);
return v___x_23_;
}
}
LEAN_EXPORT lean_object* lp_purelean_hq__04__btree__flatten__mirror_BTree_ctorElim___boxed(lean_object* v_00_u03b1_24_, lean_object* v_motive_25_, lean_object* v_ctorIdx_26_, lean_object* v_t_27_, lean_object* v_h_28_, lean_object* v_k_29_){
_start:
{
lean_object* v_res_30_; 
v_res_30_ = lp_purelean_hq__04__btree__flatten__mirror_BTree_ctorElim(v_00_u03b1_24_, v_motive_25_, v_ctorIdx_26_, v_t_27_, v_h_28_, v_k_29_);
lean_dec(v_ctorIdx_26_);
return v_res_30_;
}
}
LEAN_EXPORT lean_object* lp_purelean_hq__04__btree__flatten__mirror_BTree_leaf_elim___redArg(lean_object* v_t_31_, lean_object* v_leaf_32_){
_start:
{
lean_object* v___x_33_; 
v___x_33_ = lp_purelean_hq__04__btree__flatten__mirror_BTree_ctorElim___redArg(v_t_31_, v_leaf_32_);
return v___x_33_;
}
}
LEAN_EXPORT lean_object* lp_purelean_hq__04__btree__flatten__mirror_BTree_leaf_elim(lean_object* v_00_u03b1_34_, lean_object* v_motive_35_, lean_object* v_t_36_, lean_object* v_h_37_, lean_object* v_leaf_38_){
_start:
{
lean_object* v___x_39_; 
v___x_39_ = lp_purelean_hq__04__btree__flatten__mirror_BTree_ctorElim___redArg(v_t_36_, v_leaf_38_);
return v___x_39_;
}
}
LEAN_EXPORT lean_object* lp_purelean_hq__04__btree__flatten__mirror_BTree_node_elim___redArg(lean_object* v_t_40_, lean_object* v_node_41_){
_start:
{
lean_object* v___x_42_; 
v___x_42_ = lp_purelean_hq__04__btree__flatten__mirror_BTree_ctorElim___redArg(v_t_40_, v_node_41_);
return v___x_42_;
}
}
LEAN_EXPORT lean_object* lp_purelean_hq__04__btree__flatten__mirror_BTree_node_elim(lean_object* v_00_u03b1_43_, lean_object* v_motive_44_, lean_object* v_t_45_, lean_object* v_h_46_, lean_object* v_node_47_){
_start:
{
lean_object* v___x_48_; 
v___x_48_ = lp_purelean_hq__04__btree__flatten__mirror_BTree_ctorElim___redArg(v_t_45_, v_node_47_);
return v___x_48_;
}
}
LEAN_EXPORT lean_object* lp_purelean_hq__04__btree__flatten__mirror_mirrorT___redArg(lean_object* v_x_49_){
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
v___x_56_ = lp_purelean_hq__04__btree__flatten__mirror_mirrorT___redArg(v_a_52_);
v___x_57_ = lp_purelean_hq__04__btree__flatten__mirror_mirrorT___redArg(v_a_50_);
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
LEAN_EXPORT lean_object* lp_purelean_hq__04__btree__flatten__mirror_mirrorT(lean_object* v_00_u03b1_62_, lean_object* v_x_63_){
_start:
{
lean_object* v___x_64_; 
v___x_64_ = lp_purelean_hq__04__btree__flatten__mirror_mirrorT___redArg(v_x_63_);
return v___x_64_;
}
}
LEAN_EXPORT lean_object* lp_purelean_hq__04__btree__flatten__mirror_flattenBT___redArg(lean_object* v_x_65_){
_start:
{
if (lean_obj_tag(v_x_65_) == 0)
{
lean_object* v___x_66_; 
v___x_66_ = lean_box(0);
return v___x_66_;
}
else
{
lean_object* v_a_67_; lean_object* v_a_68_; lean_object* v_a_69_; lean_object* v___x_70_; lean_object* v___x_71_; lean_object* v___x_72_; lean_object* v___x_73_; lean_object* v___x_74_; lean_object* v___x_75_; 
v_a_67_ = lean_ctor_get(v_x_65_, 0);
v_a_68_ = lean_ctor_get(v_x_65_, 1);
v_a_69_ = lean_ctor_get(v_x_65_, 2);
v___x_70_ = lp_purelean_hq__04__btree__flatten__mirror_flattenBT___redArg(v_a_67_);
v___x_71_ = lean_box(0);
lean_inc(v_a_68_);
v___x_72_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_72_, 0, v_a_68_);
lean_ctor_set(v___x_72_, 1, v___x_71_);
v___x_73_ = l_List_appendTR___redArg(v___x_70_, v___x_72_);
v___x_74_ = lp_purelean_hq__04__btree__flatten__mirror_flattenBT___redArg(v_a_69_);
v___x_75_ = l_List_appendTR___redArg(v___x_73_, v___x_74_);
return v___x_75_;
}
}
}
LEAN_EXPORT lean_object* lp_purelean_hq__04__btree__flatten__mirror_flattenBT___redArg___boxed(lean_object* v_x_76_){
_start:
{
lean_object* v_res_77_; 
v_res_77_ = lp_purelean_hq__04__btree__flatten__mirror_flattenBT___redArg(v_x_76_);
lean_dec(v_x_76_);
return v_res_77_;
}
}
LEAN_EXPORT lean_object* lp_purelean_hq__04__btree__flatten__mirror_flattenBT(lean_object* v_00_u03b1_78_, lean_object* v_x_79_){
_start:
{
lean_object* v___x_80_; 
v___x_80_ = lp_purelean_hq__04__btree__flatten__mirror_flattenBT___redArg(v_x_79_);
return v___x_80_;
}
}
LEAN_EXPORT lean_object* lp_purelean_hq__04__btree__flatten__mirror_flattenBT___boxed(lean_object* v_00_u03b1_81_, lean_object* v_x_82_){
_start:
{
lean_object* v_res_83_; 
v_res_83_ = lp_purelean_hq__04__btree__flatten__mirror_flattenBT(v_00_u03b1_81_, v_x_82_);
lean_dec(v_x_82_);
return v_res_83_;
}
}
LEAN_EXPORT lean_object* lp_purelean_hq__06__mapAcc__correct_mapAcc___redArg(lean_object* v_f_84_, lean_object* v_x_85_, lean_object* v_x_86_){
_start:
{
if (lean_obj_tag(v_x_85_) == 0)
{
lean_object* v___x_87_; 
lean_dec(v_f_84_);
v___x_87_ = l_List_reverse___redArg(v_x_86_);
return v___x_87_;
}
else
{
lean_object* v_head_88_; lean_object* v_tail_89_; lean_object* v___x_91_; uint8_t v_isShared_92_; uint8_t v_isSharedCheck_98_; 
v_head_88_ = lean_ctor_get(v_x_85_, 0);
v_tail_89_ = lean_ctor_get(v_x_85_, 1);
v_isSharedCheck_98_ = !lean_is_exclusive(v_x_85_);
if (v_isSharedCheck_98_ == 0)
{
v___x_91_ = v_x_85_;
v_isShared_92_ = v_isSharedCheck_98_;
goto v_resetjp_90_;
}
else
{
lean_inc(v_tail_89_);
lean_inc(v_head_88_);
lean_dec(v_x_85_);
v___x_91_ = lean_box(0);
v_isShared_92_ = v_isSharedCheck_98_;
goto v_resetjp_90_;
}
v_resetjp_90_:
{
lean_object* v___x_93_; lean_object* v___x_95_; 
lean_inc(v_f_84_);
v___x_93_ = lean_apply_1(v_f_84_, v_head_88_);
if (v_isShared_92_ == 0)
{
lean_ctor_set(v___x_91_, 1, v_x_86_);
lean_ctor_set(v___x_91_, 0, v___x_93_);
v___x_95_ = v___x_91_;
goto v_reusejp_94_;
}
else
{
lean_object* v_reuseFailAlloc_97_; 
v_reuseFailAlloc_97_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_97_, 0, v___x_93_);
lean_ctor_set(v_reuseFailAlloc_97_, 1, v_x_86_);
v___x_95_ = v_reuseFailAlloc_97_;
goto v_reusejp_94_;
}
v_reusejp_94_:
{
v_x_85_ = v_tail_89_;
v_x_86_ = v___x_95_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* lp_purelean_hq__06__mapAcc__correct_mapAcc(lean_object* v_00_u03b1_99_, lean_object* v_00_u03b2_100_, lean_object* v_f_101_, lean_object* v_x_102_, lean_object* v_x_103_){
_start:
{
lean_object* v___x_104_; 
v___x_104_ = lp_purelean_hq__06__mapAcc__correct_mapAcc___redArg(v_f_101_, v_x_102_, v_x_103_);
return v___x_104_;
}
}
LEAN_EXPORT lean_object* lp_purelean_hq__11__foldl__via__foldr__cps_foldrL___redArg(lean_object* v_f_105_, lean_object* v_z_106_, lean_object* v_x_107_){
_start:
{
if (lean_obj_tag(v_x_107_) == 0)
{
lean_dec(v_f_105_);
lean_inc(v_z_106_);
return v_z_106_;
}
else
{
lean_object* v_head_108_; lean_object* v_tail_109_; lean_object* v___x_110_; lean_object* v___x_111_; 
v_head_108_ = lean_ctor_get(v_x_107_, 0);
lean_inc(v_head_108_);
v_tail_109_ = lean_ctor_get(v_x_107_, 1);
lean_inc(v_tail_109_);
lean_dec_ref_known(v_x_107_, 2);
lean_inc(v_f_105_);
v___x_110_ = lp_purelean_hq__11__foldl__via__foldr__cps_foldrL___redArg(v_f_105_, v_z_106_, v_tail_109_);
v___x_111_ = lean_apply_2(v_f_105_, v_head_108_, v___x_110_);
return v___x_111_;
}
}
}
LEAN_EXPORT lean_object* lp_purelean_hq__11__foldl__via__foldr__cps_foldrL___redArg___boxed(lean_object* v_f_112_, lean_object* v_z_113_, lean_object* v_x_114_){
_start:
{
lean_object* v_res_115_; 
v_res_115_ = lp_purelean_hq__11__foldl__via__foldr__cps_foldrL___redArg(v_f_112_, v_z_113_, v_x_114_);
lean_dec(v_z_113_);
return v_res_115_;
}
}
LEAN_EXPORT lean_object* lp_purelean_hq__11__foldl__via__foldr__cps_foldrL(lean_object* v_00_u03b1_116_, lean_object* v_00_u03b2_117_, lean_object* v_f_118_, lean_object* v_z_119_, lean_object* v_x_120_){
_start:
{
lean_object* v___x_121_; 
v___x_121_ = lp_purelean_hq__11__foldl__via__foldr__cps_foldrL___redArg(v_f_118_, v_z_119_, v_x_120_);
return v___x_121_;
}
}
LEAN_EXPORT lean_object* lp_purelean_hq__11__foldl__via__foldr__cps_foldrL___boxed(lean_object* v_00_u03b1_122_, lean_object* v_00_u03b2_123_, lean_object* v_f_124_, lean_object* v_z_125_, lean_object* v_x_126_){
_start:
{
lean_object* v_res_127_; 
v_res_127_ = lp_purelean_hq__11__foldl__via__foldr__cps_foldrL(v_00_u03b1_122_, v_00_u03b2_123_, v_f_124_, v_z_125_, v_x_126_);
lean_dec(v_z_125_);
return v_res_127_;
}
}
LEAN_EXPORT lean_object* lp_purelean_hq__11__foldl__via__foldr__cps_foldlL___redArg(lean_object* v_f_128_, lean_object* v_x_129_, lean_object* v_x_130_){
_start:
{
if (lean_obj_tag(v_x_130_) == 0)
{
lean_dec(v_f_128_);
return v_x_129_;
}
else
{
lean_object* v_head_131_; lean_object* v_tail_132_; lean_object* v___x_133_; 
v_head_131_ = lean_ctor_get(v_x_130_, 0);
lean_inc(v_head_131_);
v_tail_132_ = lean_ctor_get(v_x_130_, 1);
lean_inc(v_tail_132_);
lean_dec_ref_known(v_x_130_, 2);
lean_inc(v_f_128_);
v___x_133_ = lean_apply_2(v_f_128_, v_x_129_, v_head_131_);
v_x_129_ = v___x_133_;
v_x_130_ = v_tail_132_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* lp_purelean_hq__11__foldl__via__foldr__cps_foldlL(lean_object* v_00_u03b1_135_, lean_object* v_00_u03b2_136_, lean_object* v_f_137_, lean_object* v_x_138_, lean_object* v_x_139_){
_start:
{
lean_object* v___x_140_; 
v___x_140_ = lp_purelean_hq__11__foldl__via__foldr__cps_foldlL___redArg(v_f_137_, v_x_138_, v_x_139_);
return v___x_140_;
}
}
LEAN_EXPORT lean_object* lp_purelean_hq__12__group__commutator__inv_commG___redArg(lean_object* v_inst_141_, lean_object* v_a_142_, lean_object* v_b_143_){
_start:
{
lean_object* v_mul_144_; lean_object* v_inv_145_; lean_object* v___x_146_; lean_object* v___x_147_; lean_object* v___x_148_; lean_object* v___x_149_; lean_object* v___x_150_; 
v_mul_144_ = lean_ctor_get(v_inst_141_, 0);
lean_inc_n(v_mul_144_, 3);
v_inv_145_ = lean_ctor_get(v_inst_141_, 2);
lean_inc_n(v_inv_145_, 2);
lean_dec_ref(v_inst_141_);
lean_inc(v_b_143_);
lean_inc(v_a_142_);
v___x_146_ = lean_apply_2(v_mul_144_, v_a_142_, v_b_143_);
v___x_147_ = lean_apply_1(v_inv_145_, v_a_142_);
v___x_148_ = lean_apply_2(v_mul_144_, v___x_146_, v___x_147_);
v___x_149_ = lean_apply_1(v_inv_145_, v_b_143_);
v___x_150_ = lean_apply_2(v_mul_144_, v___x_148_, v___x_149_);
return v___x_150_;
}
}
LEAN_EXPORT lean_object* lp_purelean_hq__12__group__commutator__inv_commG(lean_object* v_G_151_, lean_object* v_inst_152_, lean_object* v_a_153_, lean_object* v_b_154_){
_start:
{
lean_object* v___x_155_; 
v___x_155_ = lp_purelean_hq__12__group__commutator__inv_commG___redArg(v_inst_152_, v_a_153_, v_b_154_);
return v___x_155_;
}
}
LEAN_EXPORT lean_object* lp_purelean_hq__13__fib__addition__formula_fibN(lean_object* v_x_156_){
_start:
{
lean_object* v_zero_157_; uint8_t v_isZero_158_; 
v_zero_157_ = lean_unsigned_to_nat(0u);
v_isZero_158_ = lean_nat_dec_eq(v_x_156_, v_zero_157_);
if (v_isZero_158_ == 1)
{
return v_zero_157_;
}
else
{
lean_object* v_one_159_; lean_object* v_n_160_; uint8_t v_isZero_161_; 
v_one_159_ = lean_unsigned_to_nat(1u);
v_n_160_ = lean_nat_sub(v_x_156_, v_one_159_);
v_isZero_161_ = lean_nat_dec_eq(v_n_160_, v_zero_157_);
if (v_isZero_161_ == 1)
{
lean_dec(v_n_160_);
return v_one_159_;
}
else
{
lean_object* v_n_162_; lean_object* v___x_163_; lean_object* v___x_164_; lean_object* v___x_165_; lean_object* v___x_166_; 
v_n_162_ = lean_nat_sub(v_n_160_, v_one_159_);
lean_dec(v_n_160_);
v___x_163_ = lp_purelean_hq__13__fib__addition__formula_fibN(v_n_162_);
v___x_164_ = lean_nat_add(v_n_162_, v_one_159_);
lean_dec(v_n_162_);
v___x_165_ = lp_purelean_hq__13__fib__addition__formula_fibN(v___x_164_);
lean_dec(v___x_164_);
v___x_166_ = lean_nat_add(v___x_163_, v___x_165_);
lean_dec(v___x_165_);
lean_dec(v___x_163_);
return v___x_166_;
}
}
}
}
LEAN_EXPORT lean_object* lp_purelean_hq__13__fib__addition__formula_fibN___boxed(lean_object* v_x_167_){
_start:
{
lean_object* v_res_168_; 
v_res_168_ = lp_purelean_hq__13__fib__addition__formula_fibN(v_x_167_);
lean_dec(v_x_167_);
return v_res_168_;
}
}
LEAN_EXPORT lean_object* lp_purelean_hq__14__arith__vm__compiler_ArithAST_ctorIdx___impl(lean_object* v_x_169_){
_start:
{
lean_object* v___x_170_; 
v___x_170_ = lean_obj_tag_nat(v_x_169_);
return v___x_170_;
}
}
LEAN_EXPORT lean_object* lp_purelean_hq__14__arith__vm__compiler_ArithAST_ctorIdx___impl___boxed(lean_object* v_x_171_){
_start:
{
lean_object* v_res_172_; 
v_res_172_ = lp_purelean_hq__14__arith__vm__compiler_ArithAST_ctorIdx___impl(v_x_171_);
lean_dec_ref(v_x_171_);
return v_res_172_;
}
}
LEAN_EXPORT lean_object* lp_purelean_hq__14__arith__vm__compiler_ArithAST_ctorElim___redArg(lean_object* v_t_173_, lean_object* v_k_174_){
_start:
{
if (lean_obj_tag(v_t_173_) == 0)
{
lean_object* v_a_175_; lean_object* v___x_176_; 
v_a_175_ = lean_ctor_get(v_t_173_, 0);
lean_inc(v_a_175_);
lean_dec_ref_known(v_t_173_, 1);
v___x_176_ = lean_apply_1(v_k_174_, v_a_175_);
return v___x_176_;
}
else
{
lean_object* v_a_177_; lean_object* v_a_178_; lean_object* v___x_179_; 
v_a_177_ = lean_ctor_get(v_t_173_, 0);
lean_inc_ref(v_a_177_);
v_a_178_ = lean_ctor_get(v_t_173_, 1);
lean_inc_ref(v_a_178_);
lean_dec_ref(v_t_173_);
v___x_179_ = lean_apply_2(v_k_174_, v_a_177_, v_a_178_);
return v___x_179_;
}
}
}
LEAN_EXPORT lean_object* lp_purelean_hq__14__arith__vm__compiler_ArithAST_ctorElim(lean_object* v_motive_180_, lean_object* v_ctorIdx_181_, lean_object* v_t_182_, lean_object* v_h_183_, lean_object* v_k_184_){
_start:
{
lean_object* v___x_185_; 
v___x_185_ = lp_purelean_hq__14__arith__vm__compiler_ArithAST_ctorElim___redArg(v_t_182_, v_k_184_);
return v___x_185_;
}
}
LEAN_EXPORT lean_object* lp_purelean_hq__14__arith__vm__compiler_ArithAST_ctorElim___boxed(lean_object* v_motive_186_, lean_object* v_ctorIdx_187_, lean_object* v_t_188_, lean_object* v_h_189_, lean_object* v_k_190_){
_start:
{
lean_object* v_res_191_; 
v_res_191_ = lp_purelean_hq__14__arith__vm__compiler_ArithAST_ctorElim(v_motive_186_, v_ctorIdx_187_, v_t_188_, v_h_189_, v_k_190_);
lean_dec(v_ctorIdx_187_);
return v_res_191_;
}
}
LEAN_EXPORT lean_object* lp_purelean_hq__14__arith__vm__compiler_ArithAST_lit_elim___redArg(lean_object* v_t_192_, lean_object* v_lit_193_){
_start:
{
lean_object* v___x_194_; 
v___x_194_ = lp_purelean_hq__14__arith__vm__compiler_ArithAST_ctorElim___redArg(v_t_192_, v_lit_193_);
return v___x_194_;
}
}
LEAN_EXPORT lean_object* lp_purelean_hq__14__arith__vm__compiler_ArithAST_lit_elim(lean_object* v_motive_195_, lean_object* v_t_196_, lean_object* v_h_197_, lean_object* v_lit_198_){
_start:
{
lean_object* v___x_199_; 
v___x_199_ = lp_purelean_hq__14__arith__vm__compiler_ArithAST_ctorElim___redArg(v_t_196_, v_lit_198_);
return v___x_199_;
}
}
LEAN_EXPORT lean_object* lp_purelean_hq__14__arith__vm__compiler_ArithAST_add_elim___redArg(lean_object* v_t_200_, lean_object* v_add_201_){
_start:
{
lean_object* v___x_202_; 
v___x_202_ = lp_purelean_hq__14__arith__vm__compiler_ArithAST_ctorElim___redArg(v_t_200_, v_add_201_);
return v___x_202_;
}
}
LEAN_EXPORT lean_object* lp_purelean_hq__14__arith__vm__compiler_ArithAST_add_elim(lean_object* v_motive_203_, lean_object* v_t_204_, lean_object* v_h_205_, lean_object* v_add_206_){
_start:
{
lean_object* v___x_207_; 
v___x_207_ = lp_purelean_hq__14__arith__vm__compiler_ArithAST_ctorElim___redArg(v_t_204_, v_add_206_);
return v___x_207_;
}
}
LEAN_EXPORT lean_object* lp_purelean_hq__14__arith__vm__compiler_ArithAST_mul_elim___redArg(lean_object* v_t_208_, lean_object* v_mul_209_){
_start:
{
lean_object* v___x_210_; 
v___x_210_ = lp_purelean_hq__14__arith__vm__compiler_ArithAST_ctorElim___redArg(v_t_208_, v_mul_209_);
return v___x_210_;
}
}
LEAN_EXPORT lean_object* lp_purelean_hq__14__arith__vm__compiler_ArithAST_mul_elim(lean_object* v_motive_211_, lean_object* v_t_212_, lean_object* v_h_213_, lean_object* v_mul_214_){
_start:
{
lean_object* v___x_215_; 
v___x_215_ = lp_purelean_hq__14__arith__vm__compiler_ArithAST_ctorElim___redArg(v_t_212_, v_mul_214_);
return v___x_215_;
}
}
LEAN_EXPORT lean_object* lp_purelean_hq__14__arith__vm__compiler_evalAST(lean_object* v_x_216_){
_start:
{
switch(lean_obj_tag(v_x_216_))
{
case 0:
{
lean_object* v_a_217_; 
v_a_217_ = lean_ctor_get(v_x_216_, 0);
lean_inc(v_a_217_);
return v_a_217_;
}
case 1:
{
lean_object* v_a_218_; lean_object* v_a_219_; lean_object* v___x_220_; lean_object* v___x_221_; lean_object* v___x_222_; 
v_a_218_ = lean_ctor_get(v_x_216_, 0);
v_a_219_ = lean_ctor_get(v_x_216_, 1);
v___x_220_ = lp_purelean_hq__14__arith__vm__compiler_evalAST(v_a_218_);
v___x_221_ = lp_purelean_hq__14__arith__vm__compiler_evalAST(v_a_219_);
v___x_222_ = lean_nat_add(v___x_220_, v___x_221_);
lean_dec(v___x_221_);
lean_dec(v___x_220_);
return v___x_222_;
}
default: 
{
lean_object* v_a_223_; lean_object* v_a_224_; lean_object* v___x_225_; lean_object* v___x_226_; lean_object* v___x_227_; 
v_a_223_ = lean_ctor_get(v_x_216_, 0);
v_a_224_ = lean_ctor_get(v_x_216_, 1);
v___x_225_ = lp_purelean_hq__14__arith__vm__compiler_evalAST(v_a_223_);
v___x_226_ = lp_purelean_hq__14__arith__vm__compiler_evalAST(v_a_224_);
v___x_227_ = lean_nat_mul(v___x_225_, v___x_226_);
lean_dec(v___x_226_);
lean_dec(v___x_225_);
return v___x_227_;
}
}
}
}
LEAN_EXPORT lean_object* lp_purelean_hq__14__arith__vm__compiler_evalAST___boxed(lean_object* v_x_228_){
_start:
{
lean_object* v_res_229_; 
v_res_229_ = lp_purelean_hq__14__arith__vm__compiler_evalAST(v_x_228_);
lean_dec_ref(v_x_228_);
return v_res_229_;
}
}
LEAN_EXPORT lean_object* lp_purelean_hq__14__arith__vm__compiler_OpInstr_ctorIdx___impl(lean_object* v_x_230_){
_start:
{
lean_object* v___x_231_; 
v___x_231_ = lean_obj_tag_nat(v_x_230_);
return v___x_231_;
}
}
LEAN_EXPORT lean_object* lp_purelean_hq__14__arith__vm__compiler_OpInstr_ctorIdx___impl___boxed(lean_object* v_x_232_){
_start:
{
lean_object* v_res_233_; 
v_res_233_ = lp_purelean_hq__14__arith__vm__compiler_OpInstr_ctorIdx___impl(v_x_232_);
lean_dec(v_x_232_);
return v_res_233_;
}
}
LEAN_EXPORT lean_object* lp_purelean_hq__14__arith__vm__compiler_OpInstr_ctorElim___redArg(lean_object* v_t_234_, lean_object* v_k_235_){
_start:
{
if (lean_obj_tag(v_t_234_) == 0)
{
lean_object* v_a_236_; lean_object* v___x_237_; 
v_a_236_ = lean_ctor_get(v_t_234_, 0);
lean_inc(v_a_236_);
lean_dec_ref_known(v_t_234_, 1);
v___x_237_ = lean_apply_1(v_k_235_, v_a_236_);
return v___x_237_;
}
else
{
lean_dec(v_t_234_);
return v_k_235_;
}
}
}
LEAN_EXPORT lean_object* lp_purelean_hq__14__arith__vm__compiler_OpInstr_ctorElim(lean_object* v_motive_238_, lean_object* v_ctorIdx_239_, lean_object* v_t_240_, lean_object* v_h_241_, lean_object* v_k_242_){
_start:
{
lean_object* v___x_243_; 
v___x_243_ = lp_purelean_hq__14__arith__vm__compiler_OpInstr_ctorElim___redArg(v_t_240_, v_k_242_);
return v___x_243_;
}
}
LEAN_EXPORT lean_object* lp_purelean_hq__14__arith__vm__compiler_OpInstr_ctorElim___boxed(lean_object* v_motive_244_, lean_object* v_ctorIdx_245_, lean_object* v_t_246_, lean_object* v_h_247_, lean_object* v_k_248_){
_start:
{
lean_object* v_res_249_; 
v_res_249_ = lp_purelean_hq__14__arith__vm__compiler_OpInstr_ctorElim(v_motive_244_, v_ctorIdx_245_, v_t_246_, v_h_247_, v_k_248_);
lean_dec(v_ctorIdx_245_);
return v_res_249_;
}
}
LEAN_EXPORT lean_object* lp_purelean_hq__14__arith__vm__compiler_OpInstr_push_elim___redArg(lean_object* v_t_250_, lean_object* v_push_251_){
_start:
{
lean_object* v___x_252_; 
v___x_252_ = lp_purelean_hq__14__arith__vm__compiler_OpInstr_ctorElim___redArg(v_t_250_, v_push_251_);
return v___x_252_;
}
}
LEAN_EXPORT lean_object* lp_purelean_hq__14__arith__vm__compiler_OpInstr_push_elim(lean_object* v_motive_253_, lean_object* v_t_254_, lean_object* v_h_255_, lean_object* v_push_256_){
_start:
{
lean_object* v___x_257_; 
v___x_257_ = lp_purelean_hq__14__arith__vm__compiler_OpInstr_ctorElim___redArg(v_t_254_, v_push_256_);
return v___x_257_;
}
}
LEAN_EXPORT lean_object* lp_purelean_hq__14__arith__vm__compiler_OpInstr_addOp_elim___redArg(lean_object* v_t_258_, lean_object* v_addOp_259_){
_start:
{
lean_object* v___x_260_; 
v___x_260_ = lp_purelean_hq__14__arith__vm__compiler_OpInstr_ctorElim___redArg(v_t_258_, v_addOp_259_);
return v___x_260_;
}
}
LEAN_EXPORT lean_object* lp_purelean_hq__14__arith__vm__compiler_OpInstr_addOp_elim(lean_object* v_motive_261_, lean_object* v_t_262_, lean_object* v_h_263_, lean_object* v_addOp_264_){
_start:
{
lean_object* v___x_265_; 
v___x_265_ = lp_purelean_hq__14__arith__vm__compiler_OpInstr_ctorElim___redArg(v_t_262_, v_addOp_264_);
return v___x_265_;
}
}
LEAN_EXPORT lean_object* lp_purelean_hq__14__arith__vm__compiler_OpInstr_mulOp_elim___redArg(lean_object* v_t_266_, lean_object* v_mulOp_267_){
_start:
{
lean_object* v___x_268_; 
v___x_268_ = lp_purelean_hq__14__arith__vm__compiler_OpInstr_ctorElim___redArg(v_t_266_, v_mulOp_267_);
return v___x_268_;
}
}
LEAN_EXPORT lean_object* lp_purelean_hq__14__arith__vm__compiler_OpInstr_mulOp_elim(lean_object* v_motive_269_, lean_object* v_t_270_, lean_object* v_h_271_, lean_object* v_mulOp_272_){
_start:
{
lean_object* v___x_273_; 
v___x_273_ = lp_purelean_hq__14__arith__vm__compiler_OpInstr_ctorElim___redArg(v_t_270_, v_mulOp_272_);
return v___x_273_;
}
}
LEAN_EXPORT lean_object* lp_purelean_hq__14__arith__vm__compiler_execOps(lean_object* v_x_274_, lean_object* v_x_275_){
_start:
{
if (lean_obj_tag(v_x_274_) == 0)
{
return v_x_275_;
}
else
{
lean_object* v_head_276_; 
v_head_276_ = lean_ctor_get(v_x_274_, 0);
switch(lean_obj_tag(v_head_276_))
{
case 0:
{
lean_object* v_tail_277_; lean_object* v___x_279_; uint8_t v_isShared_280_; uint8_t v_isSharedCheck_286_; 
lean_inc_ref(v_head_276_);
v_tail_277_ = lean_ctor_get(v_x_274_, 1);
v_isSharedCheck_286_ = !lean_is_exclusive(v_x_274_);
if (v_isSharedCheck_286_ == 0)
{
lean_object* v_unused_287_; 
v_unused_287_ = lean_ctor_get(v_x_274_, 0);
lean_dec(v_unused_287_);
v___x_279_ = v_x_274_;
v_isShared_280_ = v_isSharedCheck_286_;
goto v_resetjp_278_;
}
else
{
lean_inc(v_tail_277_);
lean_dec(v_x_274_);
v___x_279_ = lean_box(0);
v_isShared_280_ = v_isSharedCheck_286_;
goto v_resetjp_278_;
}
v_resetjp_278_:
{
lean_object* v_a_281_; lean_object* v___x_283_; 
v_a_281_ = lean_ctor_get(v_head_276_, 0);
lean_inc(v_a_281_);
lean_dec_ref_known(v_head_276_, 1);
if (v_isShared_280_ == 0)
{
lean_ctor_set(v___x_279_, 1, v_x_275_);
lean_ctor_set(v___x_279_, 0, v_a_281_);
v___x_283_ = v___x_279_;
goto v_reusejp_282_;
}
else
{
lean_object* v_reuseFailAlloc_285_; 
v_reuseFailAlloc_285_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_285_, 0, v_a_281_);
lean_ctor_set(v_reuseFailAlloc_285_, 1, v_x_275_);
v___x_283_ = v_reuseFailAlloc_285_;
goto v_reusejp_282_;
}
v_reusejp_282_:
{
v_x_274_ = v_tail_277_;
v_x_275_ = v___x_283_;
goto _start;
}
}
}
case 1:
{
if (lean_obj_tag(v_x_275_) == 1)
{
lean_object* v_tail_288_; 
v_tail_288_ = lean_ctor_get(v_x_275_, 1);
lean_inc(v_tail_288_);
if (lean_obj_tag(v_tail_288_) == 1)
{
lean_object* v_tail_289_; lean_object* v_head_290_; lean_object* v_head_291_; lean_object* v_tail_292_; lean_object* v___x_294_; uint8_t v_isShared_295_; uint8_t v_isSharedCheck_301_; 
v_tail_289_ = lean_ctor_get(v_x_274_, 1);
lean_inc(v_tail_289_);
lean_dec_ref_known(v_x_274_, 2);
v_head_290_ = lean_ctor_get(v_x_275_, 0);
lean_inc(v_head_290_);
lean_dec_ref_known(v_x_275_, 2);
v_head_291_ = lean_ctor_get(v_tail_288_, 0);
v_tail_292_ = lean_ctor_get(v_tail_288_, 1);
v_isSharedCheck_301_ = !lean_is_exclusive(v_tail_288_);
if (v_isSharedCheck_301_ == 0)
{
v___x_294_ = v_tail_288_;
v_isShared_295_ = v_isSharedCheck_301_;
goto v_resetjp_293_;
}
else
{
lean_inc(v_tail_292_);
lean_inc(v_head_291_);
lean_dec(v_tail_288_);
v___x_294_ = lean_box(0);
v_isShared_295_ = v_isSharedCheck_301_;
goto v_resetjp_293_;
}
v_resetjp_293_:
{
lean_object* v___x_296_; lean_object* v___x_298_; 
v___x_296_ = lean_nat_add(v_head_291_, v_head_290_);
lean_dec(v_head_290_);
lean_dec(v_head_291_);
if (v_isShared_295_ == 0)
{
lean_ctor_set(v___x_294_, 0, v___x_296_);
v___x_298_ = v___x_294_;
goto v_reusejp_297_;
}
else
{
lean_object* v_reuseFailAlloc_300_; 
v_reuseFailAlloc_300_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_300_, 0, v___x_296_);
lean_ctor_set(v_reuseFailAlloc_300_, 1, v_tail_292_);
v___x_298_ = v_reuseFailAlloc_300_;
goto v_reusejp_297_;
}
v_reusejp_297_:
{
v_x_274_ = v_tail_289_;
v_x_275_ = v___x_298_;
goto _start;
}
}
}
else
{
lean_object* v_tail_302_; 
lean_dec(v_tail_288_);
v_tail_302_ = lean_ctor_get(v_x_274_, 1);
lean_inc(v_tail_302_);
lean_dec_ref_known(v_x_274_, 2);
v_x_274_ = v_tail_302_;
goto _start;
}
}
else
{
lean_object* v_tail_304_; 
v_tail_304_ = lean_ctor_get(v_x_274_, 1);
lean_inc(v_tail_304_);
lean_dec_ref_known(v_x_274_, 2);
v_x_274_ = v_tail_304_;
goto _start;
}
}
default: 
{
if (lean_obj_tag(v_x_275_) == 1)
{
lean_object* v_tail_306_; 
v_tail_306_ = lean_ctor_get(v_x_275_, 1);
lean_inc(v_tail_306_);
if (lean_obj_tag(v_tail_306_) == 1)
{
lean_object* v_tail_307_; lean_object* v_head_308_; lean_object* v_head_309_; lean_object* v_tail_310_; lean_object* v___x_312_; uint8_t v_isShared_313_; uint8_t v_isSharedCheck_319_; 
v_tail_307_ = lean_ctor_get(v_x_274_, 1);
lean_inc(v_tail_307_);
lean_dec_ref_known(v_x_274_, 2);
v_head_308_ = lean_ctor_get(v_x_275_, 0);
lean_inc(v_head_308_);
lean_dec_ref_known(v_x_275_, 2);
v_head_309_ = lean_ctor_get(v_tail_306_, 0);
v_tail_310_ = lean_ctor_get(v_tail_306_, 1);
v_isSharedCheck_319_ = !lean_is_exclusive(v_tail_306_);
if (v_isSharedCheck_319_ == 0)
{
v___x_312_ = v_tail_306_;
v_isShared_313_ = v_isSharedCheck_319_;
goto v_resetjp_311_;
}
else
{
lean_inc(v_tail_310_);
lean_inc(v_head_309_);
lean_dec(v_tail_306_);
v___x_312_ = lean_box(0);
v_isShared_313_ = v_isSharedCheck_319_;
goto v_resetjp_311_;
}
v_resetjp_311_:
{
lean_object* v___x_314_; lean_object* v___x_316_; 
v___x_314_ = lean_nat_mul(v_head_309_, v_head_308_);
lean_dec(v_head_308_);
lean_dec(v_head_309_);
if (v_isShared_313_ == 0)
{
lean_ctor_set(v___x_312_, 0, v___x_314_);
v___x_316_ = v___x_312_;
goto v_reusejp_315_;
}
else
{
lean_object* v_reuseFailAlloc_318_; 
v_reuseFailAlloc_318_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_318_, 0, v___x_314_);
lean_ctor_set(v_reuseFailAlloc_318_, 1, v_tail_310_);
v___x_316_ = v_reuseFailAlloc_318_;
goto v_reusejp_315_;
}
v_reusejp_315_:
{
v_x_274_ = v_tail_307_;
v_x_275_ = v___x_316_;
goto _start;
}
}
}
else
{
lean_object* v_tail_320_; 
lean_dec(v_tail_306_);
v_tail_320_ = lean_ctor_get(v_x_274_, 1);
lean_inc(v_tail_320_);
lean_dec_ref_known(v_x_274_, 2);
v_x_274_ = v_tail_320_;
goto _start;
}
}
else
{
lean_object* v_tail_322_; 
v_tail_322_ = lean_ctor_get(v_x_274_, 1);
lean_inc(v_tail_322_);
lean_dec_ref_known(v_x_274_, 2);
v_x_274_ = v_tail_322_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* lp_purelean_hq__14__arith__vm__compiler_compileAST(lean_object* v_x_330_){
_start:
{
switch(lean_obj_tag(v_x_330_))
{
case 0:
{
lean_object* v_a_331_; lean_object* v___x_333_; uint8_t v_isShared_334_; uint8_t v_isSharedCheck_340_; 
v_a_331_ = lean_ctor_get(v_x_330_, 0);
v_isSharedCheck_340_ = !lean_is_exclusive(v_x_330_);
if (v_isSharedCheck_340_ == 0)
{
v___x_333_ = v_x_330_;
v_isShared_334_ = v_isSharedCheck_340_;
goto v_resetjp_332_;
}
else
{
lean_inc(v_a_331_);
lean_dec(v_x_330_);
v___x_333_ = lean_box(0);
v_isShared_334_ = v_isSharedCheck_340_;
goto v_resetjp_332_;
}
v_resetjp_332_:
{
lean_object* v___x_336_; 
if (v_isShared_334_ == 0)
{
v___x_336_ = v___x_333_;
goto v_reusejp_335_;
}
else
{
lean_object* v_reuseFailAlloc_339_; 
v_reuseFailAlloc_339_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_339_, 0, v_a_331_);
v___x_336_ = v_reuseFailAlloc_339_;
goto v_reusejp_335_;
}
v_reusejp_335_:
{
lean_object* v___x_337_; lean_object* v___x_338_; 
v___x_337_ = lean_box(0);
v___x_338_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_338_, 0, v___x_336_);
lean_ctor_set(v___x_338_, 1, v___x_337_);
return v___x_338_;
}
}
}
case 1:
{
lean_object* v_a_341_; lean_object* v_a_342_; lean_object* v___x_343_; lean_object* v___x_344_; lean_object* v___x_345_; lean_object* v___x_346_; lean_object* v___x_347_; 
v_a_341_ = lean_ctor_get(v_x_330_, 0);
lean_inc_ref(v_a_341_);
v_a_342_ = lean_ctor_get(v_x_330_, 1);
lean_inc_ref(v_a_342_);
lean_dec_ref_known(v_x_330_, 2);
v___x_343_ = lp_purelean_hq__14__arith__vm__compiler_compileAST(v_a_341_);
v___x_344_ = lp_purelean_hq__14__arith__vm__compiler_compileAST(v_a_342_);
v___x_345_ = l_List_appendTR___redArg(v___x_343_, v___x_344_);
v___x_346_ = ((lean_object*)(lp_purelean_hq__14__arith__vm__compiler_compileAST___closed__0));
v___x_347_ = l_List_appendTR___redArg(v___x_345_, v___x_346_);
return v___x_347_;
}
default: 
{
lean_object* v_a_348_; lean_object* v_a_349_; lean_object* v___x_350_; lean_object* v___x_351_; lean_object* v___x_352_; lean_object* v___x_353_; lean_object* v___x_354_; 
v_a_348_ = lean_ctor_get(v_x_330_, 0);
lean_inc_ref(v_a_348_);
v_a_349_ = lean_ctor_get(v_x_330_, 1);
lean_inc_ref(v_a_349_);
lean_dec_ref_known(v_x_330_, 2);
v___x_350_ = lp_purelean_hq__14__arith__vm__compiler_compileAST(v_a_348_);
v___x_351_ = lp_purelean_hq__14__arith__vm__compiler_compileAST(v_a_349_);
v___x_352_ = l_List_appendTR___redArg(v___x_350_, v___x_351_);
v___x_353_ = ((lean_object*)(lp_purelean_hq__14__arith__vm__compiler_compileAST___closed__1));
v___x_354_ = l_List_appendTR___redArg(v___x_352_, v___x_353_);
return v___x_354_;
}
}
}
}
LEAN_EXPORT lean_object* lp_purelean_hq__15__nicomachus__sum__cubes_sumCubes(lean_object* v_x_355_){
_start:
{
lean_object* v_zero_356_; uint8_t v_isZero_357_; 
v_zero_356_ = lean_unsigned_to_nat(0u);
v_isZero_357_ = lean_nat_dec_eq(v_x_355_, v_zero_356_);
if (v_isZero_357_ == 1)
{
return v_zero_356_;
}
else
{
lean_object* v_one_358_; lean_object* v_n_359_; lean_object* v___x_360_; lean_object* v___x_361_; lean_object* v___x_362_; lean_object* v___x_363_; lean_object* v___x_364_; 
v_one_358_ = lean_unsigned_to_nat(1u);
v_n_359_ = lean_nat_sub(v_x_355_, v_one_358_);
v___x_360_ = lp_purelean_hq__15__nicomachus__sum__cubes_sumCubes(v_n_359_);
v___x_361_ = lean_nat_add(v_n_359_, v_one_358_);
lean_dec(v_n_359_);
v___x_362_ = lean_nat_mul(v___x_361_, v___x_361_);
v___x_363_ = lean_nat_mul(v___x_362_, v___x_361_);
lean_dec(v___x_361_);
lean_dec(v___x_362_);
v___x_364_ = lean_nat_add(v___x_360_, v___x_363_);
lean_dec(v___x_363_);
lean_dec(v___x_360_);
return v___x_364_;
}
}
}
LEAN_EXPORT lean_object* lp_purelean_hq__15__nicomachus__sum__cubes_sumCubes___boxed(lean_object* v_x_365_){
_start:
{
lean_object* v_res_366_; 
v_res_366_ = lp_purelean_hq__15__nicomachus__sum__cubes_sumCubes(v_x_365_);
lean_dec(v_x_365_);
return v_res_366_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_purelean_PureLean_HardBenchmarks(uint8_t builtin) {
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
