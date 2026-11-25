// Lean compiler output
// Module: PureLean.HoldoutBenchmarks
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
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_obj_tag_nat(lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_purelean_eval__08__iter__periodic_iterFn___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_purelean_eval__08__iter__periodic_iterFn___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_purelean_eval__08__iter__periodic_iterFn(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_purelean_eval__08__iter__periodic_iterFn___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_purelean_eval__09__lenAcc__correct_lenAcc___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_purelean_eval__09__lenAcc__correct_lenAcc___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_purelean_eval__09__lenAcc__correct_lenAcc(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_purelean_eval__09__lenAcc__correct_lenAcc___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_purelean_eval__10__btree__leaves__pos_BTree_ctorIdx___impl___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_purelean_eval__10__btree__leaves__pos_BTree_ctorIdx___impl___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_purelean_eval__10__btree__leaves__pos_BTree_ctorIdx___impl(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_purelean_eval__10__btree__leaves__pos_BTree_ctorIdx___impl___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_purelean_eval__10__btree__leaves__pos_BTree_ctorElim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_purelean_eval__10__btree__leaves__pos_BTree_ctorElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_purelean_eval__10__btree__leaves__pos_BTree_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_purelean_eval__10__btree__leaves__pos_BTree_leaf_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_purelean_eval__10__btree__leaves__pos_BTree_leaf_elim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_purelean_eval__10__btree__leaves__pos_BTree_node_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_purelean_eval__10__btree__leaves__pos_BTree_node_elim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_purelean_eval__10__btree__leaves__pos_countLeaves___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_purelean_eval__10__btree__leaves__pos_countLeaves___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_purelean_eval__10__btree__leaves__pos_countLeaves(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_purelean_eval__10__btree__leaves__pos_countLeaves___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_purelean_eval__10__btree__leaves__pos_countNodes___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_purelean_eval__10__btree__leaves__pos_countNodes___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_purelean_eval__10__btree__leaves__pos_countNodes(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_purelean_eval__10__btree__leaves__pos_countNodes___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_purelean_eval__12__sum__squares__six_sumSq(lean_object*);
LEAN_EXPORT lean_object* lp_purelean_eval__12__sum__squares__six_sumSq___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_purelean_eval__08__iter__periodic_iterFn___redArg(lean_object* v_f_1_, lean_object* v_x_2_, lean_object* v_x_3_){
_start:
{
lean_object* v_zero_4_; uint8_t v_isZero_5_; 
v_zero_4_ = lean_unsigned_to_nat(0u);
v_isZero_5_ = lean_nat_dec_eq(v_x_2_, v_zero_4_);
if (v_isZero_5_ == 1)
{
lean_dec(v_f_1_);
lean_inc(v_x_3_);
return v_x_3_;
}
else
{
lean_object* v_one_6_; lean_object* v_n_7_; lean_object* v___x_8_; lean_object* v___x_9_; 
v_one_6_ = lean_unsigned_to_nat(1u);
v_n_7_ = lean_nat_sub(v_x_2_, v_one_6_);
lean_inc(v_f_1_);
v___x_8_ = lp_purelean_eval__08__iter__periodic_iterFn___redArg(v_f_1_, v_n_7_, v_x_3_);
lean_dec(v_n_7_);
v___x_9_ = lean_apply_1(v_f_1_, v___x_8_);
return v___x_9_;
}
}
}
LEAN_EXPORT lean_object* lp_purelean_eval__08__iter__periodic_iterFn___redArg___boxed(lean_object* v_f_10_, lean_object* v_x_11_, lean_object* v_x_12_){
_start:
{
lean_object* v_res_13_; 
v_res_13_ = lp_purelean_eval__08__iter__periodic_iterFn___redArg(v_f_10_, v_x_11_, v_x_12_);
lean_dec(v_x_12_);
lean_dec(v_x_11_);
return v_res_13_;
}
}
LEAN_EXPORT lean_object* lp_purelean_eval__08__iter__periodic_iterFn(lean_object* v_00_u03b1_14_, lean_object* v_f_15_, lean_object* v_x_16_, lean_object* v_x_17_){
_start:
{
lean_object* v___x_18_; 
v___x_18_ = lp_purelean_eval__08__iter__periodic_iterFn___redArg(v_f_15_, v_x_16_, v_x_17_);
return v___x_18_;
}
}
LEAN_EXPORT lean_object* lp_purelean_eval__08__iter__periodic_iterFn___boxed(lean_object* v_00_u03b1_19_, lean_object* v_f_20_, lean_object* v_x_21_, lean_object* v_x_22_){
_start:
{
lean_object* v_res_23_; 
v_res_23_ = lp_purelean_eval__08__iter__periodic_iterFn(v_00_u03b1_19_, v_f_20_, v_x_21_, v_x_22_);
lean_dec(v_x_22_);
lean_dec(v_x_21_);
return v_res_23_;
}
}
LEAN_EXPORT lean_object* lp_purelean_eval__09__lenAcc__correct_lenAcc___redArg(lean_object* v_x_24_, lean_object* v_x_25_){
_start:
{
if (lean_obj_tag(v_x_24_) == 0)
{
return v_x_25_;
}
else
{
lean_object* v_tail_26_; lean_object* v___x_27_; lean_object* v___x_28_; 
v_tail_26_ = lean_ctor_get(v_x_24_, 1);
v___x_27_ = lean_unsigned_to_nat(1u);
v___x_28_ = lean_nat_add(v_x_25_, v___x_27_);
lean_dec(v_x_25_);
v_x_24_ = v_tail_26_;
v_x_25_ = v___x_28_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* lp_purelean_eval__09__lenAcc__correct_lenAcc___redArg___boxed(lean_object* v_x_30_, lean_object* v_x_31_){
_start:
{
lean_object* v_res_32_; 
v_res_32_ = lp_purelean_eval__09__lenAcc__correct_lenAcc___redArg(v_x_30_, v_x_31_);
lean_dec(v_x_30_);
return v_res_32_;
}
}
LEAN_EXPORT lean_object* lp_purelean_eval__09__lenAcc__correct_lenAcc(lean_object* v_00_u03b1_33_, lean_object* v_x_34_, lean_object* v_x_35_){
_start:
{
lean_object* v___x_36_; 
v___x_36_ = lp_purelean_eval__09__lenAcc__correct_lenAcc___redArg(v_x_34_, v_x_35_);
return v___x_36_;
}
}
LEAN_EXPORT lean_object* lp_purelean_eval__09__lenAcc__correct_lenAcc___boxed(lean_object* v_00_u03b1_37_, lean_object* v_x_38_, lean_object* v_x_39_){
_start:
{
lean_object* v_res_40_; 
v_res_40_ = lp_purelean_eval__09__lenAcc__correct_lenAcc(v_00_u03b1_37_, v_x_38_, v_x_39_);
lean_dec(v_x_38_);
return v_res_40_;
}
}
LEAN_EXPORT lean_object* lp_purelean_eval__10__btree__leaves__pos_BTree_ctorIdx___impl___redArg(lean_object* v_x_41_){
_start:
{
lean_object* v___x_42_; 
v___x_42_ = lean_obj_tag_nat(v_x_41_);
return v___x_42_;
}
}
LEAN_EXPORT lean_object* lp_purelean_eval__10__btree__leaves__pos_BTree_ctorIdx___impl___redArg___boxed(lean_object* v_x_43_){
_start:
{
lean_object* v_res_44_; 
v_res_44_ = lp_purelean_eval__10__btree__leaves__pos_BTree_ctorIdx___impl___redArg(v_x_43_);
lean_dec(v_x_43_);
return v_res_44_;
}
}
LEAN_EXPORT lean_object* lp_purelean_eval__10__btree__leaves__pos_BTree_ctorIdx___impl(lean_object* v_00_u03b1_45_, lean_object* v_x_46_){
_start:
{
lean_object* v___x_47_; 
v___x_47_ = lean_obj_tag_nat(v_x_46_);
return v___x_47_;
}
}
LEAN_EXPORT lean_object* lp_purelean_eval__10__btree__leaves__pos_BTree_ctorIdx___impl___boxed(lean_object* v_00_u03b1_48_, lean_object* v_x_49_){
_start:
{
lean_object* v_res_50_; 
v_res_50_ = lp_purelean_eval__10__btree__leaves__pos_BTree_ctorIdx___impl(v_00_u03b1_48_, v_x_49_);
lean_dec(v_x_49_);
return v_res_50_;
}
}
LEAN_EXPORT lean_object* lp_purelean_eval__10__btree__leaves__pos_BTree_ctorElim___redArg(lean_object* v_t_51_, lean_object* v_k_52_){
_start:
{
if (lean_obj_tag(v_t_51_) == 0)
{
return v_k_52_;
}
else
{
lean_object* v_a_53_; lean_object* v_a_54_; lean_object* v_a_55_; lean_object* v___x_56_; 
v_a_53_ = lean_ctor_get(v_t_51_, 0);
lean_inc(v_a_53_);
v_a_54_ = lean_ctor_get(v_t_51_, 1);
lean_inc(v_a_54_);
v_a_55_ = lean_ctor_get(v_t_51_, 2);
lean_inc(v_a_55_);
lean_dec_ref_known(v_t_51_, 3);
v___x_56_ = lean_apply_3(v_k_52_, v_a_53_, v_a_54_, v_a_55_);
return v___x_56_;
}
}
}
LEAN_EXPORT lean_object* lp_purelean_eval__10__btree__leaves__pos_BTree_ctorElim(lean_object* v_00_u03b1_57_, lean_object* v_motive_58_, lean_object* v_ctorIdx_59_, lean_object* v_t_60_, lean_object* v_h_61_, lean_object* v_k_62_){
_start:
{
lean_object* v___x_63_; 
v___x_63_ = lp_purelean_eval__10__btree__leaves__pos_BTree_ctorElim___redArg(v_t_60_, v_k_62_);
return v___x_63_;
}
}
LEAN_EXPORT lean_object* lp_purelean_eval__10__btree__leaves__pos_BTree_ctorElim___boxed(lean_object* v_00_u03b1_64_, lean_object* v_motive_65_, lean_object* v_ctorIdx_66_, lean_object* v_t_67_, lean_object* v_h_68_, lean_object* v_k_69_){
_start:
{
lean_object* v_res_70_; 
v_res_70_ = lp_purelean_eval__10__btree__leaves__pos_BTree_ctorElim(v_00_u03b1_64_, v_motive_65_, v_ctorIdx_66_, v_t_67_, v_h_68_, v_k_69_);
lean_dec(v_ctorIdx_66_);
return v_res_70_;
}
}
LEAN_EXPORT lean_object* lp_purelean_eval__10__btree__leaves__pos_BTree_leaf_elim___redArg(lean_object* v_t_71_, lean_object* v_leaf_72_){
_start:
{
lean_object* v___x_73_; 
v___x_73_ = lp_purelean_eval__10__btree__leaves__pos_BTree_ctorElim___redArg(v_t_71_, v_leaf_72_);
return v___x_73_;
}
}
LEAN_EXPORT lean_object* lp_purelean_eval__10__btree__leaves__pos_BTree_leaf_elim(lean_object* v_00_u03b1_74_, lean_object* v_motive_75_, lean_object* v_t_76_, lean_object* v_h_77_, lean_object* v_leaf_78_){
_start:
{
lean_object* v___x_79_; 
v___x_79_ = lp_purelean_eval__10__btree__leaves__pos_BTree_ctorElim___redArg(v_t_76_, v_leaf_78_);
return v___x_79_;
}
}
LEAN_EXPORT lean_object* lp_purelean_eval__10__btree__leaves__pos_BTree_node_elim___redArg(lean_object* v_t_80_, lean_object* v_node_81_){
_start:
{
lean_object* v___x_82_; 
v___x_82_ = lp_purelean_eval__10__btree__leaves__pos_BTree_ctorElim___redArg(v_t_80_, v_node_81_);
return v___x_82_;
}
}
LEAN_EXPORT lean_object* lp_purelean_eval__10__btree__leaves__pos_BTree_node_elim(lean_object* v_00_u03b1_83_, lean_object* v_motive_84_, lean_object* v_t_85_, lean_object* v_h_86_, lean_object* v_node_87_){
_start:
{
lean_object* v___x_88_; 
v___x_88_ = lp_purelean_eval__10__btree__leaves__pos_BTree_ctorElim___redArg(v_t_85_, v_node_87_);
return v___x_88_;
}
}
LEAN_EXPORT lean_object* lp_purelean_eval__10__btree__leaves__pos_countLeaves___redArg(lean_object* v_x_89_){
_start:
{
if (lean_obj_tag(v_x_89_) == 0)
{
lean_object* v___x_90_; 
v___x_90_ = lean_unsigned_to_nat(1u);
return v___x_90_;
}
else
{
lean_object* v_a_91_; lean_object* v_a_92_; lean_object* v___x_93_; lean_object* v___x_94_; lean_object* v___x_95_; 
v_a_91_ = lean_ctor_get(v_x_89_, 0);
v_a_92_ = lean_ctor_get(v_x_89_, 2);
v___x_93_ = lp_purelean_eval__10__btree__leaves__pos_countLeaves___redArg(v_a_91_);
v___x_94_ = lp_purelean_eval__10__btree__leaves__pos_countLeaves___redArg(v_a_92_);
v___x_95_ = lean_nat_add(v___x_93_, v___x_94_);
lean_dec(v___x_94_);
lean_dec(v___x_93_);
return v___x_95_;
}
}
}
LEAN_EXPORT lean_object* lp_purelean_eval__10__btree__leaves__pos_countLeaves___redArg___boxed(lean_object* v_x_96_){
_start:
{
lean_object* v_res_97_; 
v_res_97_ = lp_purelean_eval__10__btree__leaves__pos_countLeaves___redArg(v_x_96_);
lean_dec(v_x_96_);
return v_res_97_;
}
}
LEAN_EXPORT lean_object* lp_purelean_eval__10__btree__leaves__pos_countLeaves(lean_object* v_00_u03b1_98_, lean_object* v_x_99_){
_start:
{
lean_object* v___x_100_; 
v___x_100_ = lp_purelean_eval__10__btree__leaves__pos_countLeaves___redArg(v_x_99_);
return v___x_100_;
}
}
LEAN_EXPORT lean_object* lp_purelean_eval__10__btree__leaves__pos_countLeaves___boxed(lean_object* v_00_u03b1_101_, lean_object* v_x_102_){
_start:
{
lean_object* v_res_103_; 
v_res_103_ = lp_purelean_eval__10__btree__leaves__pos_countLeaves(v_00_u03b1_101_, v_x_102_);
lean_dec(v_x_102_);
return v_res_103_;
}
}
LEAN_EXPORT lean_object* lp_purelean_eval__10__btree__leaves__pos_countNodes___redArg(lean_object* v_x_104_){
_start:
{
if (lean_obj_tag(v_x_104_) == 0)
{
lean_object* v___x_105_; 
v___x_105_ = lean_unsigned_to_nat(0u);
return v___x_105_;
}
else
{
lean_object* v_a_106_; lean_object* v_a_107_; lean_object* v___x_108_; lean_object* v___x_109_; lean_object* v___x_110_; lean_object* v___x_111_; lean_object* v___x_112_; 
v_a_106_ = lean_ctor_get(v_x_104_, 0);
v_a_107_ = lean_ctor_get(v_x_104_, 2);
v___x_108_ = lean_unsigned_to_nat(1u);
v___x_109_ = lp_purelean_eval__10__btree__leaves__pos_countNodes___redArg(v_a_106_);
v___x_110_ = lean_nat_add(v___x_108_, v___x_109_);
lean_dec(v___x_109_);
v___x_111_ = lp_purelean_eval__10__btree__leaves__pos_countNodes___redArg(v_a_107_);
v___x_112_ = lean_nat_add(v___x_110_, v___x_111_);
lean_dec(v___x_111_);
lean_dec(v___x_110_);
return v___x_112_;
}
}
}
LEAN_EXPORT lean_object* lp_purelean_eval__10__btree__leaves__pos_countNodes___redArg___boxed(lean_object* v_x_113_){
_start:
{
lean_object* v_res_114_; 
v_res_114_ = lp_purelean_eval__10__btree__leaves__pos_countNodes___redArg(v_x_113_);
lean_dec(v_x_113_);
return v_res_114_;
}
}
LEAN_EXPORT lean_object* lp_purelean_eval__10__btree__leaves__pos_countNodes(lean_object* v_00_u03b1_115_, lean_object* v_x_116_){
_start:
{
lean_object* v___x_117_; 
v___x_117_ = lp_purelean_eval__10__btree__leaves__pos_countNodes___redArg(v_x_116_);
return v___x_117_;
}
}
LEAN_EXPORT lean_object* lp_purelean_eval__10__btree__leaves__pos_countNodes___boxed(lean_object* v_00_u03b1_118_, lean_object* v_x_119_){
_start:
{
lean_object* v_res_120_; 
v_res_120_ = lp_purelean_eval__10__btree__leaves__pos_countNodes(v_00_u03b1_118_, v_x_119_);
lean_dec(v_x_119_);
return v_res_120_;
}
}
LEAN_EXPORT lean_object* lp_purelean_eval__12__sum__squares__six_sumSq(lean_object* v_x_121_){
_start:
{
lean_object* v_zero_122_; uint8_t v_isZero_123_; 
v_zero_122_ = lean_unsigned_to_nat(0u);
v_isZero_123_ = lean_nat_dec_eq(v_x_121_, v_zero_122_);
if (v_isZero_123_ == 1)
{
return v_zero_122_;
}
else
{
lean_object* v_one_124_; lean_object* v_n_125_; lean_object* v___x_126_; lean_object* v___x_127_; lean_object* v___x_128_; lean_object* v___x_129_; 
v_one_124_ = lean_unsigned_to_nat(1u);
v_n_125_ = lean_nat_sub(v_x_121_, v_one_124_);
v___x_126_ = lp_purelean_eval__12__sum__squares__six_sumSq(v_n_125_);
v___x_127_ = lean_nat_add(v_n_125_, v_one_124_);
lean_dec(v_n_125_);
v___x_128_ = lean_nat_mul(v___x_127_, v___x_127_);
lean_dec(v___x_127_);
v___x_129_ = lean_nat_add(v___x_126_, v___x_128_);
lean_dec(v___x_128_);
lean_dec(v___x_126_);
return v___x_129_;
}
}
}
LEAN_EXPORT lean_object* lp_purelean_eval__12__sum__squares__six_sumSq___boxed(lean_object* v_x_130_){
_start:
{
lean_object* v_res_131_; 
v_res_131_ = lp_purelean_eval__12__sum__squares__six_sumSq(v_x_130_);
lean_dec(v_x_130_);
return v_res_131_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_purelean_PureLean_HoldoutBenchmarks(uint8_t builtin) {
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
