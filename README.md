# Assignment

## Add the following to complete and execute the model
### 1. Write the following invariants: (20 marks)
* Each post is owned by at most one user
* A user cannot be his or her own friend
* Friendship is a symmetric relation
* Server capacity is positive
* Servers cannot exceed their capacity
### 2. Explore different (alternative) replication strategies for posts: (8 marks)
* Each post is stored in at most one server
* Each post is stored in at least two servers
### 3. Specify the following operations ensuring they preserve the above invariants (20 marks)
* addPost[n1, n2:DistributedSN,u:User,p:Post] add post p by user u.
* delPost[n1, n2:DistributedSN,u:User,p:Post] delete post p from user u.
* addFriend[n1, n2:DistributedSN,u,v:User] add v as friend of u.
* addServer[n1, n2:DistributedSN,s:Server] add new server s to network n1.
* delServer[n1, n2:DistributedSN,s:Server] delete server s from network n1.
### 4. Check the following algebraic properties of these operations: (8 marks)
* delPost undoes addPost
* delServer undoes addServer