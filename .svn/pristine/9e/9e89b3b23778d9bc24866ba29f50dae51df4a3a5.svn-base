//retruns SUBSET if second set is SUBSET
//retruns SUPERSET if second set is SUPERSET
//retruns EQ if sets are the same
//otherwise defines order
CompareValues
Rule::subsumes(Atom** l1,  Atom** l1end,Atom** l2,  Atom** l2end){
  if(l1end-l1>=l2end-l2){
	return subsumesGr(l1, l1end, l2, l2end);	  
  }
  CompareValue ret=subsumesGr(l2, l2end, l1, l1end);
  if(ret==LTH)
	return GTH;
  if(ret==GTH)
	return LTH;
  if(ret==EQ)
	return EQ;
  if(ret==SUBSET)
	return SUPERSET
  else
	return SUBSET;
}

CompareValues
Rule::subsumesGr(Atom** sup,  Atom** supend,Atom** sub,  Atom** subend){
  assert(supend-sup>=subend-sub);//size of super set is always greater than hypothetic subset
  Atom** a_sup=sup;
  for(Atom** a_sub=sub; a_sub<subend;a_sub++){
	while(supend-a_sup>=subend-a_sub //super array is still larger than subarray
		  && (*a_sub)->id>(*a_sup)->id){
	  a_sup++;
	}
	if(supend-a_sup>=subend-a_sub&&(*a_sub)->id==(*a_sup)->id  )
	  a_sup++;
	else{//there may not be subsumption either it will not be enough atoms
	  if(supend-sup>subend-sub||(*a_sup)->id > (*a_sub)->id)
		return GTH;
	  else // only in this case it holds:	if((*a_sup)->id < (*a_sub)->id)
		return LTH; //the sizes of the arrays are identical and hence 
		  //the difference is in last elements
	}
  }
  if(supend-sup==subend-sub)
	return EQ;
  else
	return SUBSET;
}
