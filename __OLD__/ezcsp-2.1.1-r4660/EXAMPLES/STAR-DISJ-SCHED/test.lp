task(a_a,60). task(a_n,30). task(a_o,2). task(a_s,5). task(b_a,75). task(b_n,3).
task(b_o,15). task(b_s,10). task(c_a,5). task(c_n,15). task(c_o,10).
task(c_s,30). task(d_a,90). task(d_n,1). task(d_o,1). task(d_s,1). 

est(a_a,700). est(a_n,700). est(a_o,700). est(a_s,700). est(b_a,715).
est(b_n,715). est(b_o,715). est(b_s,715). est(c_a,715). est(c_n,715).
est(c_o,715). est(c_s,715). est(d_a,800). est(d_n,800). est(d_o,800).
est(d_s,800).  

let(a_a,1000). let(a_n,1000). let(a_o,1000). let(a_s,1000). let(b_a,1000).
let(b_n,1000). let(b_o,1000). let(b_s,1000). let(c_a,1000). let(c_n,1000).
let(c_o,1000). let(c_s,1000). let(d_a,1000). let(d_n,1000). let(d_o,1000).
let(d_s,1000). 

disj(a_a,a_n). disj(a_a,a_o). disj(a_a,a_s). disj(a_n,a_o). disj(a_n,a_s).
disj(a_o,a_s). disj(b_a,b_n). disj(b_a,b_o). disj(b_a,b_s). disj(b_n,b_o).
disj(b_n,b_s). disj(b_o,b_s). disj(c_a,c_n). disj(c_a,c_o). disj(c_a,c_s).
disj(c_n,c_o). disj(c_n,c_s). disj(c_o,c_s). disj(d_a,d_n). disj(d_a,d_o).
disj(d_a,d_s). disj(d_n,d_o). disj(d_n,d_s). disj(d_o,d_s). disj(a_a,b_a).
disj(a_a,c_a). disj(a_a,d_a). disj(b_a,c_a). disj(b_a,d_a). disj(c_a,d_a).
disj(a_n,b_n). disj(a_n,c_n). disj(a_n,d_n). disj(b_n,c_n). disj(b_n,d_n).
disj(c_n,d_n). disj(a_o,b_o). disj(a_o,c_o). disj(a_o,d_o). disj(b_o,c_o).
disj(b_o,d_o). disj(c_o,d_o). disj(a_s,b_s). disj(a_s,c_s). disj(a_s,d_s).
disj(b_s,c_s). disj(b_s,d_s). disj(c_s,d_s). 
