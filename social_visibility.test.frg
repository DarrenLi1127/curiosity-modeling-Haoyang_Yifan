#lang forge/froglet

open "social_visibility.frg"

test suite for wellformed {
    test expect {
        // Two users can be friends with each other.
        valid_structure: {
            some disj u1, u2: User | {
                u1.friends[u2] = True
                u2.friends[u1] = True
                wellformed
            }
        } for 5 Int is sat

        // A user cannot be friends with themselves.
        self_friend: {
            some u: User | {
                u.friends[u] = True
                wellformed
            }
        } for 5 Int is unsat

        // A user cannot be both a friend and blocked simultaneously.
        friend_and_blocked: {
            some disj u1, u2: User | {
                u1.friends[u2] = True
                u1.blocked[u2] = True
                wellformed
            }
        } for 5 Int is unsat

        // A user cannot mute themselves.
        self_mute: {
            some u: User | {
                u.muted[u] = True
                wellformed
            }
        } for 5 Int is unsat
    }
}

test suite for canSee {
    test expect {
        // Author can always see their own private posts, even if moments are closed.
        author_god_mode: {
            wellformed
            some u: User, p: Post | {
                p.author = u
                p.visibility = Private
                u.moments_closed = True 
                canSee[u, p]            
            }
        } for 5 Int is sat

        // Private posts are strictly invisible to friends, even without global restrictions.
        private_hidden_from_friends: {
            wellformed
            some disj owner, friend: User, p: Post | {
                owner.friends[friend] = True
                owner.moments_closed = False
                p.author = owner
                p.visibility = Private
                canSee[friend, p] 
            }
        } for 5 Int is unsat

        // Only friends in the 'allowed_viewers' list can see 'SpecificFriends' posts.
        specific_friends_logic: {
            wellformed
            some disj owner, allowed_f, blocked_f: User, p: Post | {
                owner.friends[allowed_f] = True
                owner.friends[blocked_f] = True
                
                owner.moments_closed = False
                owner.limit_recent_10 = False
                
                p.author = owner
                p.visibility = SpecificFriends
                p.allowed_viewers[allowed_f] = True
                p.allowed_viewers[blocked_f] = False
                
                canSee[allowed_f, p] and not canSee[blocked_f, p]
            }
        } for 5 Int is sat
        
        // Friends in the 'excluded_viewers' list cannot see 'ExcludeFriends' posts.
        exclude_friends_logic: {
            wellformed
            some disj owner, normal_f, excluded_f: User, p: Post | {
                owner.friends[normal_f] = True 
                owner.friends[excluded_f] = True
                owner.moments_closed = False 
                owner.limit_recent_10 = False
                
                p.author = owner 
                p.visibility = ExcludeFriends 
                p.excluded_viewers[excluded_f] = True 
                p.excluded_viewers[normal_f] = False
                
                canSee[normal_f, p] and not canSee[excluded_f, p]
            }
        } for 5 Int is sat

        // Blocked users cannot see anything, even public posts with stranger access enabled.
        blocklist_absolute_defense: {
            wellformed
            some disj owner, hater: User, p: Post | {
                owner.blocked[hater] = True 
                
                owner.moments_closed = False
                owner.stranger_see_recent = True 
                
                p.author = owner
                p.visibility = Public 
                isRecent[p]           
                
                canSee[hater, p]
            }
        } for 5 Int is unsat 
        
        // If viewer mutes author, viewer sees nothing.
        muted_absolute_defense: {
            wellformed
            some disj owner, annoyed_friend: User, p: Post | {
                owner.friends[annoyed_friend] = True
                annoyed_friend.muted[owner] = True 
                
                owner.moments_closed = False
                p.author = owner 
                p.visibility = Public 
                isRecent[p]
                
                canSee[annoyed_friend, p] 
            }
        } for 5 Int is unsat

        // 'FriendsOnly' posts are visible to friends but hidden from strangers.
        friends_only_logic: {
            wellformed
            some disj owner, friend, stranger: User, p: Post | {
                owner.friends[friend] = True
                owner.friends[stranger] != True
                
                owner.moments_closed = False
                owner.limit_recent_10 = False
                owner.stranger_see_recent = True 
                
                p.author = owner
                p.visibility = FriendsOnly 
                isRecent[p]
                
                canSee[friend, p] and not canSee[stranger, p]
            }
        } for 5 Int is sat

        // Strangers cannot see anything if 'stranger_see_recent' is turned off.
        stranger_access_disabled: {
            wellformed
            some disj owner, stranger: User, p: Post | {
                owner.friends[stranger] = False
                owner.stranger_see_recent = False 
                
                p.author = owner
                p.visibility = Public
                isRecent[p]
                
                canSee[stranger, p] 
            }
        } for 5 Int is unsat
    }
}

test suite for isRecent {
    test expect {
        // Closing moments globally hides all posts from friends.
        moments_closed_blocks_all: {
            wellformed
            some disj owner, friend: User, p: Post | {
                owner.friends[friend] = True
                p.author = owner
                p.visibility = Public 
                
                owner.moments_closed = True 
                
                canSee[friend, p] 
            }
        } for 5 Int is unsat 

        // 'limit_recent_10' hides old posts but keeps new posts visible to friends.
        limit_recent_10_blocks_old: {
            wellformed
            some disj owner, friend: User |
            some disj p_new, p_old: Post | {
                owner.friends[friend] = True
                owner.moments_closed = False
                owner.limit_recent_10 = True 
                
                p_new.author = owner and p_new.visibility = Public and p_new.timestamp = 10
                p_old.author = owner and p_old.visibility = Public and p_old.timestamp = 1
                
                isRecent[p_new]      
                not isRecent[p_old]  
                
                canSee[friend, p_new] and not canSee[friend, p_old]
            }
        } for 5 Int, 12 Post is sat

        // Strangers can only see recent posts, and only if 'stranger_see_recent' is true.
        stranger_recent_logic: {
            wellformed
            some disj owner, stranger: User |
            some disj p_new, p_old: Post | {
                owner.friends[stranger] = False 
                owner.moments_closed = False
                owner.stranger_see_recent = True
                
                p_new.author = owner and p_new.visibility = Public and p_new.timestamp = 10
                p_old.author = owner and p_old.visibility = Public and p_old.timestamp = 1
                
                isRecent[p_new]
                not isRecent[p_old] 
                
                canSee[stranger, p_new] and not canSee[stranger, p_old]
            }
        } for 5 Int, 12 Post is sat
    }
}