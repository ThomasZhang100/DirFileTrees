/*--------------------------------------------------------------------*/
/* checkerDT.c                                                        */
/* Author:                                                            */
/*--------------------------------------------------------------------*/

#include <assert.h>
#include <stdio.h>
#include <string.h>
#include "checkerDT.h"
#include "dynarray.h"
#include "path.h"



/* see checkerDT.h for specification */
boolean CheckerDT_Node_isValid(Node_T oNNode) {
   Node_T oNParent;
   Path_T oPNPath;
   Path_T oPPPath;
   size_t i; 
   Node_T prevChild = NULL;
   Node_T currChild = NULL;

   /* Sample check: a NULL pointer is not a valid node */
   if(oNNode == NULL) {
      fprintf(stderr, "A node is a NULL pointer\n");
      return FALSE;
   }

   /* Sample check: parent's path must be the longest possible
      proper prefix of the node's path */
   oNParent = Node_getParent(oNNode);
   if(oNParent != NULL) {
      oPNPath = Node_getPath(oNNode);
      oPPPath = Node_getPath(oNParent);

      if(Path_getSharedPrefixDepth(oPNPath, oPPPath) !=
         Path_getDepth(oPNPath) - 1 || Path_getSharedPrefixDepth(oPNPath, oPPPath) !=
         Path_getDepth(oPPPath)) {
         fprintf(stderr, "P-C nodes don't have P-C paths: (%s) (%s)\n",
                 Path_getPathname(oPPPath), Path_getPathname(oPNPath));
         return FALSE;
      }
   }

   /*Check that a node's children are stored in lexicogrpahical order*/
   for(i = 1; i < Node_getNumChildren(oNNode); i++)
   {
      Node_getChild(oNNode, i-1, &prevChild);
      Node_getChild(oNNode, i, &currChild);
      if(Path_comparePath(Node_getPath(prevChild), Node_getPath(currChild)) > 0)
      {
         fprintf(stderr, "Children not stored lexicographically\n");
         return FALSE;
      }
   }

   return TRUE;
}

/*
   Performs a pre-order traversal of the tree rooted at oNNode .
   Returns FALSE if a broken invariant is found and
   returns TRUE otherwise, taking into account the existence of 
   oNHigherNode (which is oNNode or an ancestor of oNNode).

   You may want to change this function's return type or
   parameter list to facilitate constructing your checks.
   If you do, you should update this function comment.
*/
static boolean CheckerDT_treeCheck(Node_T oNNode, Node_T oNHigherNode) {
   size_t ulIndex;
   Path_T oHNPath;
   Path_T oNPath;

   if(oNNode!= NULL) {

      /* Sample check on each node: node must be valid */
      /* If not, pass that failure back up immediately */
      if(!CheckerDT_Node_isValid(oNNode))
         return FALSE;

      oHNPath = Node_getPath(oNHigherNode);
      oNPath = Node_getPath(oNNode);

      if(Path_getSharedPrefixDepth(oHNPath, oNPath) !=
         Path_getDepth(oHNPath)) {
         fprintf(stderr, "Largest shared prefix depth of an Ancestor anc Child is not the depth of the ancestor: (%s) (%s)\n",
                 Path_getPathname(oNPath), Path_getPathname(oHNPath));
         return FALSE;
      }

      /* Recur on every child of oNNode */
      for(ulIndex = 0; ulIndex < Node_getNumChildren(oNNode); ulIndex++)
      {
         Node_T oNChild = NULL;
         int iStatus = Node_getChild(oNNode, ulIndex, &oNChild);

         if(iStatus != SUCCESS) {
            fprintf(stderr, "getNumChildren claims more children than getChild returns\n");
            return FALSE;
         }

         if(oNChild == NULL) {
            fprintf(stderr, "getChild returned NULL for an index that getNumChildren claimed was valid.\n");
            return FALSE;
         }

         if(Node_getParent(oNChild) != oNNode) {
            fprintf(stderr, "The parent of the child of a node (getParent of getChild of the node) didn't return the original node.\n");
            return FALSE;
         }

         /* if recurring down one subtree results in a failed check
            farther down, passes the failure back up immediately */
         if(!CheckerDT_treeCheck(oNChild, oNHigherNode))
            return FALSE;
      }
   }
   return TRUE;
}

/* see checkerDT.h for specification */
boolean CheckerDT_isValid(boolean bIsInitialized, Node_T oNRoot,
                          size_t ulCount) {

   /* Sample check on a top-level data structure invariant:
      if the DT is not initialized, its count should be 0. */
   if(!bIsInitialized)
      if(ulCount != 0) {
         fprintf(stderr, "Not initialized, but count is not 0\n");
         return FALSE;
      }

   /* Now checks invariants recursively at each node from the root. */
   return CheckerDT_treeCheck(oNRoot, oNRoot);
}
