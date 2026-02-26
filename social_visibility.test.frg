#lang forge/froglet

open "social_visibility.frg"


test suite for wellformed {
    test expect {
        // 互加好友基础测试
        valid_structure: {
            some disj u1, u2: User | {
                u1.friends[u2] = True
                u2.friends[u1] = True
                wellformed
            }
        } for 5 Int is sat

        // 自己加自己为好友
        self_friend: {
            some u: User | {
                u.friends[u] = True
                wellformed
            }
        } for 5 Int is unsat

        friend_and_blocked: {
            some disj u1, u2: User | {
                u1.friends[u2] = True
                u1.blocked[u2] = True
                wellformed
            }
        } for 5 Int is unsat
    }
}

test suite for canSee {
    test expect {
        // 【就算我一键停用了朋友圈，我发的私密贴我自己依然能看见
        author_god_mode: {
            wellformed
            some u: User, p: Post | {
                p.author = u
                p.visibility = Private
                u.moments_closed = True 
                canSee[u, p]            
            }
        } for 5 Int is sat

        // 部分可见”功能：拉两个好友，一个放白名单，一个不放。
        // 白名单里能看，不在名单里的就算也是好友也看不了
        specific_friends_logic: {
            wellformed
            some disj owner, allowed_f, blocked_f: User, p: Post | {
                owner.friends[allowed_f] = True
                owner.friends[blocked_f] = True
                
                // 确保全局开关没捣乱
                owner.moments_closed = False
                owner.limit_recent_10 = False
                
                p.author = owner
                p.visibility = SpecificFriends
                p.allowed_viewers[allowed_f] = True
                p.allowed_viewers[blocked_f] = False
                
                // allowed_f能看 且 blocked_f看不了
                canSee[allowed_f, p] and not canSee[blocked_f, p]
            }
        } for 5 Int is sat

        // 被拉黑的人即使用户允许陌生人查看，也无法查看公开贴
        blocklist_absolute_defense: {
            wellformed
            some disj owner, hater: User, p: Post | {
                owner.blocked[hater] = True // owner把hater拉黑了
                
                owner.moments_closed = False
                owner.stranger_see_recent = True // 允许陌生人看
                
                p.author = owner
                p.visibility = Public // 哪怕是公开贴
                isRecent[p]           // 哪怕是最新的一条
                
                // hater依然看不了！如果他能看，这个用例就会sat（变成unsat代表防御成功）
                canSee[hater, p]
            }
        } for 5 Int is unsat 
        
        // 仅好友可见测试 (FriendsOnly)
        friends_only_logic: {
            wellformed
            some disj owner, friend, stranger: User, p: Post | {
                owner.friends[friend] = True
                owner.friends[stranger] != True
                
                owner.moments_closed = False
                owner.limit_recent_10 = False
                owner.stranger_see_recent = True // 即便允许陌生人看十条
                
                p.author = owner
                p.visibility = FriendsOnly // 但这篇帖子是“仅好友”
                isRecent[p]
                
                // 好友能看，陌生人不能看
                canSee[friend, p] and not canSee[stranger, p]
            }
        } for 5 Int is sat
    }
}

test suite for isRecent {
    test expect {
        //一键关闭朋友圈的绝对防御！
        // 我发了个公开贴，但我把朋友圈关了。
        // 谁也看不见
        moments_closed_blocks_all: {
            wellformed
            some disj owner, friend: User, p: Post | {
                owner.friends[friend] = True
                p.author = owner
                p.visibility = Public 
                
                owner.moments_closed = True // 狠心关停朋友圈
                
                canSee[friend, p] 
            }
        } for 5 Int is unsat 

        // 开启“仅展示最近十条”的过滤效果
        // 发一条新帖和一条早就过期被挤出去的老帖。
        // 就算这俩都是公开贴，好友也只能看到新的，看不了老的
        limit_recent_10_blocks_old: {
            wellformed
            some disj owner, friend: User |
            some disj p_new, p_old: Post | {
                owner.friends[friend] = True
                owner.moments_closed = False
                owner.limit_recent_10 = True // 开启仅展示最近十条
                
                p_new.author = owner and p_new.visibility = Public and p_new.timestamp = 10
                p_old.author = owner and p_old.visibility = Public and p_old.timestamp = 1
                
                isRecent[p_new]      // 保证新帖在10条内
                not isRecent[p_old]  // 强制老帖过期（不在10条内）
                
                canSee[friend, p_new] and not canSee[friend, p_old]
            }
        } for 5 Int, 12 Post is sat  // <--- 给了 12 个帖子的预算，不然 Forge 凑不够把老帖挤出前十的数量

        // 陌生人测试
        // 完全不认识的陌生人。作者打开了“允许陌生人看十条”。
        // 跟好友一样，陌生人能看到新帖，但绝对看不了过期的老帖
        stranger_recent_logic: {
            wellformed
            some disj owner, stranger: User |
            some disj p_new, p_old: Post | {
                owner.friends[stranger] = False // 确认是路人
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