#include <MyASTConsumer.h>

MyASTConsumer::MyASTConsumer(Rewriter &Rewrite, MyHolder &H, Rewriter &rewriter, std::map<int, goto_contractort*> *contractors_map)
        : rv(Rewrite, H, rewriter,contractors_map), TheHolder(H)
{

}

bool MyASTConsumer::HandleTopLevelDecl(DeclGroupRef d)
{
	for (DeclGroupRef::iterator b = d.begin(), e = d.end(); b != e; ++b)
	{
		rv.TraverseDecl(*b);
	}
	return true; // keep going
}

MyASTConsumer::~MyASTConsumer()
{
};
