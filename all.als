



sig DistributedSN{
    // Every SN has 0 or more Users,
    users : set User,

    // SN has 0 or more posts
    posts: set Post
}
sig User{
    // Every User can post 0 or more Posts
    posts: set Post
}

sig Post{
        // Every post belong to 0 1 Parent
        parent : lone Post
}

run {} for 2 but exactly 1 DistributedSN