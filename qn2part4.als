open qn2part3

check addThenDeleteIsUndo {
    all n1, n2, n3 : DistributedSN, u : User, p : Post |
        invariant[n1] and
        addPost[n1,n2,u,p] and delPost[n2,n3,u,p] implies
            n1.posts = n3.posts
}


//pred addPost[n1, n2:DistributedSN,u:User,p:Post] // add post p by user u.
//pred delPost[n1, n2:DistributedSN,u:User,p:Post] //delete post p from user u.
//addFriend[n1, n2:DistributedSN,u,v:User] //add v as friend of u.
//addServer[n1, n2:DistributedSN,s:Server] //add new server s to network n1.
// delServer[n1, n2:DistributedSN,s:Server] //delete server s from network n1.