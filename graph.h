#ifndef GRAPHSCC_H
#define GRAPHSCC_H
struct Vertex
{  
  long          name;   // Vertex name
  vector<Vertex *> adj;    // Adjacent vertices
  int              color;  // Can be 3 values 0-white
                             //1 -gray
                             //2 -black

  int              cc;  // number specifying which connected component
                        // the vertex belongs to
  // int              ccDouble;  // number specifying which connected component
  //                    // the vertex belongs to

  int              f;   //finishing time needed for Strongly connected components
  
  vector<Vertex *> pred;    // Adjacent vertices
    Vertex( long nm ) : name( nm )
      { color = 0; 
	    cc=-1;
	    //    ccDouble=-1;

	  }

    void reset( )
      { color = 0; 
	    cc=-1; 
	    //ccDouble=-1;
	  }
  
};

typedef map<long,Vertex *> vmap;
typedef pair<long,Vertex *> vpair;


class Graph
{
  public:
    Graph( ) { }
    ~Graph( ){deleteGraph( );}
    void addEdge( long sourceName, long destName );
	void addEdgeCC( long sourceName, long destName );
    bool DFS();
	bool DFS_visit(Vertex * v);
    int  DFSCC(int* atomCC);
	void DFS_visitCC(Vertex * v);
    int  DFSStrongCC(int* atomCC, int* finaltimes, int size);
    void  DFSClassic(int* finaltimes);
	int DFS_visitClassic(Vertex * v, int time);
      
	int numberOfVertex(){

	  return allVertices.size( );
	}
    Vertex * getVertex( long vertexName );
  
    void clearAll( );
	void deleteGraph( );

    vmap vertexMap;
    vector<Vertex *> allVertices;
};
