#ifndef EZCSP_SEARCH_STATE_H
#define EZCSP_SEARCH_STATE_H

#include <string>

void load_search_state_asp(std::string SEARCH_STATE,std::string PREV_ASP_MODELS);
void append_search_state_csp(std::string SEARCH_STATE,std::string PL_TRANS);
void store_search_state(std::string SEARCH_STATE,std::string PREV_ASP_MODELS,std::string PL_TRANS,bool csp_state_valid);

#endif /* EZCSP_SEARCH_STATE_H */
