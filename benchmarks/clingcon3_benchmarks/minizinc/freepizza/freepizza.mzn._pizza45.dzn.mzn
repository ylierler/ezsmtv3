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




n = 140;
price = [8207,7654,6143,7834,6163,1706,9347,795,8208,8296,1207,6461,3521,2904,1062,2462,1075,483,4638,9073,5521,6367,9598,9349,7812,9387,4213,1337,8643,6785,2032,4539,5621,1580,4093,7521,9991,5053,4143,7718,4237,3203,9788,5022,5407,1865,6182,2134,8955,9720,8536,4012,9860,8599,3744,2515,7178,9664,1050,8367,6832,5979,1689,4031,3016,2416,6347,295,7464,9496,5065,8227,8556,5647,3264,8667,6917,5550,2971,6848,1449,8961,3492,4619,5178,127,1553,2755,882,1567,5605,3044,5932,930,7889,8415,7312,8943,682,1820,1699,7628,1810,4426,4222,4681,4917,4742,8570,5621,7956,5618,2354,2858,7544,4162,5798,4800,9627,4633,6245,8394,5695,2233,7842,5725,4954,6301,4075,6560,2131,3190,7417,5590,8379,671,4862,959,6302,2654];
m = 4;
buy = [7,9,9,1];
free = [6,5,9,7];
