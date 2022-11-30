% pizza voucher problem
%
% pizzas to order
%    13 25 17 12 9
% vouchers
%    1+1  2+1
% you pay for the most expensive pizzas when using a voucher.

int: n; % number of pizzas
set of int: PIZZA = 1..n;
array[PIZZA] of int: price;   % price of each pizza

int: m; % number of vouchers
set of int: VOUCHER = 1..m;
array[VOUCHER] of int: buy;   % buy this many to use voucher
array[VOUCHER] of int: free;  % get this many free

set of int: ASSIGN = -m .. m; % -i pizza is assigned to buy of voucher i
                              %  i pizza is assigned to free of voucher i
                              %  0 no voucher used on pizza

array[PIZZA] of var ASSIGN: how;
array[VOUCHER] of var bool: used;

% assign right number of pizzas to buy order
constraint forall(v in VOUCHER)(used[v] <-> sum(p in PIZZA)(how[p] = -v) >= buy[v]);
constraint forall(v in VOUCHER)(sum(p in PIZZA)(how[p] = -v) <= used[v]*buy[v]);
% assign not too many pizzas to free order
constraint forall(v in VOUCHER)(sum(p in PIZZA)(how[p] = v) <= used[v]*free[v]);

% pizzas assigned to free are cheaper than pizzas assigned to buy
constraint forall(p1, p2 in PIZZA)((how[p1] < how[p2] /\ how[p1] = -how[p2]) 
                                   -> price[p2] <= price[p1]);


% symmetry breaking
%constraint forall(v1, v2 in VOUCHER where v1 < v2 /\ buy[v1] = buy[v2] /\ free[v1] = free[v2])
%                 (forall(p1, p2 in PIZZA where price[p1] < price[p2])
%                        (how[p1] = -v2 -> how[p2] != -v1));

                  




int: total = sum(price);
var 0..total: objective = sum(p in PIZZA)((how[p] <= 0)*price[p]);

solve :: int_search(how, input_order, indomain_min, complete)
      minimize objective;

output  
  ["how = "++show(how)++";\nobjective = "++show(objective)++";\n"];




n = 190;
price = [5585,7452,7268,8058,6988,5530,6223,4808,3988,9169,262,2472,5910,2194,6567,3402,3003,6646,1204,8290,2845,3470,7698,2566,5947,6164,2895,7419,864,4509,3131,7155,6299,582,936,30,43,5498,5524,3888,8264,4703,3053,8102,9868,4098,3312,6420,7707,3737,8118,4039,9332,2146,9799,3967,2656,667,8183,7294,1536,7158,3813,9397,9989,6160,4815,6633,7128,781,8536,9256,1165,7869,8099,6373,6479,1245,389,3403,8753,1495,5427,4082,4323,861,7600,3982,7670,5857,8949,9945,4620,3664,8752,6895,3648,9478,5070,8121,8657,3797,7712,6796,6307,4465,9327,9564,1026,7712,6037,2794,8087,8746,2110,1865,3718,6395,4900,8598,2194,8457,5331,9313,1541,5689,7946,2239,8523,935,480,1448,7737,5486,9870,2400,3307,8848,1915,6756,9326,3235,1916,8300,2837,4636,5814,6858,108,6103,8466,6049,3908,3399,9661,2603,5783,3852,6202,2360,6692,7189,1652,8484,117,3185,440,549,9366,9472,323,6944,158,9668,2422,6694,7916,9933,2702,4328,7479,1945,4064,7174,5260,1115,83,7867,883,6057];
m = 8;
buy = [8,8,7,8,7,7,7,8];
free = [7,7,0,7,0,0,0,7];
