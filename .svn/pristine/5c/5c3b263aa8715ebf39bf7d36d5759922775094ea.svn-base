#include "graphSCC.h"
inline
void Graph::addEdge(long sourceName, long destName )
{
    Vertex * v = getVertex( sourceName );
    Vertex * w = getVertex( destName );
    v->adj.push_back( w );

}
inline
void Graph::addEdgeCC(long sourceName, long destName )
{
    Vertex * v = getVertex( sourceName );
    Vertex * w = getVertex( destName );
    v->adj.push_back( w );
    w->adj.push_back( v );
}


// If vertexName is not present, add it to vertexMap
// In either case, return the Vertex
inline
Vertex * Graph::getVertex( long vertexName )
{
    vmap::iterator itr = vertexMap.find( vertexName );

    if( itr == vertexMap.end( ) )
    {
        Vertex *newv = new Vertex( vertexName );
        allVertices.push_back( newv );
        vertexMap.insert( vpair( vertexName, newv ) );
        return newv;
    }
    return (*itr).second;
}

inline
void Graph::clearAll( )
{
  vertexMap.clear();
}

void Graph::deleteGraph(){
  vertexMap.clear();
  for( unsigned int i = 0; i < allVertices.size( ); i++ )
	if(allVertices[i]!=NULL){
       delete  allVertices[ i ];
	   allVertices[ i ]=NULL;
	}


}

bool Graph::DFS( ){
  for( unsigned int i = 0; i<allVertices.size( );i++){
	Vertex * v =  allVertices[ i ];
	if(v->color==0)
	  if(!DFS_visit(v))
		return false;

  }
  return true;
}

void Graph::DFSClassic(int* final ){
  int time =0;
  for( unsigned int i = 0; i<allVertices.size( );i++){
	Vertex * v =  allVertices[ i ];
	if(v->color==0)
	 time = DFS_visitClassic(v,time);
		
  }
  for(unsigned int i =0; i<allVertices.size( );i++){
	Vertex * v =  allVertices[ i ];
	final[i]= v->f;

  }



  return ;
}
int Graph::DFS_visitClassic(Vertex * v, int time){
  v->color=1; //gray
  //  time++;
  for(unsigned  int j = 0; j < v->adj.size( ); j++ )
	{
       Vertex *w = v->adj[ j ];
	   w->cc=v->cc;
	   if (w->color==0){		 
		 w->pred.push_back(v);
		 time= DFS_visitClassic(w, time);
		 
	   }
	}
  v->color=2;
  v->f=time;
  time++;
  return time;
}


int Graph::DFSCC(int* atomCC){
  int k=0;
 
  for( unsigned int i = 0; i<allVertices.size( );i++){
	Vertex * v =  allVertices[ i ];
	if(v->color==0){
	  v->cc=k;
	  k++; 
	  DFS_visitCC(v);
	}
  }

  for( unsigned int i = 0; i<allVertices.size( );i++){
	Vertex * v =  allVertices[ i ];

	atomCC[v->name]=v->cc;
  }
  return k; // return number of connected components
}

int Graph::DFSStrongCC(int* atomCC, int* final, int size){
  int k=0;
  //  unsigned   int size = allVertices.size( );
  int *finaltimesback = new int[size];

  for(int i = 0; i<size;i++){

	finaltimesback[final[i]]=i;
  }
  for(int i = size-1; i>=0;i--){
	Vertex * v =  allVertices[ finaltimesback[i] ];

	if(v->color==0){
	  v->cc=k;
	  k++; 
	  DFS_visitCC(v);
	}
  
  }

  
  for( unsigned int i = 0; i<allVertices.size( );i++){
	Vertex * v =  allVertices[ i ];
	atomCC[v->name]=v->cc;
  }
  
  return k; // return number of connected components
}

void Graph::DFS_visitCC(Vertex * v){
  v->color=1;
  for( unsigned int j = 0; j < v->adj.size( ); j++ )
	{
       Vertex *w = v->adj[ j ];
	   if (w->color==0){		 
		 w->cc=v->cc;
		 w->pred.push_back(v);
		 DFS_visitCC(w);
		 
	   }
	}
  v->color=2;
  return;
}

bool Graph::DFS_visit(Vertex * v){
  v->color=1;
  for( unsigned int j = 0; j < v->adj.size( ); j++ )
	{
       Vertex *w = v->adj[ j ];
	   if (w->color==0){
		 w->pred.push_back(v);
		 if(!DFS_visit(w))
		   return false;

	   }
	   else if (w->color==1){ 



		 return false;
		 
	   }
	}
  v->color=2;
  return true;
}

