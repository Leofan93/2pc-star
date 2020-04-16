/*
 *
 * Copyright 2017-2018 549477611@qq.com(xiaoyu)
 *
 * This copyrighted material is made available to anyone wishing to use, modify,
 * copy, or redistribute it subject to the terms and conditions of the GNU
 * Lesser General Public License, as published by the Free Software Foundation.
 *
 * This program is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of MERCHANTABILITY
 * or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU Lesser General Public License
 * for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with this distribution; if not, see <http://www.gnu.org/licenses/>.
 *
 */

package org.dromara.raincat.manager.config;

import org.dromara.raincat.common.netty.bean.TxTransactionItem;
import io.netty.channel.Channel;
import lombok.Data;

import java.util.List;

/**
 * ChannelSender.
 * @author xiaoyu
 */
@Data
public class ChannelSender {

    /**
     * 模块netty 长连接渠道.
     */
    private Channel channel;

    /**
     * txManger的域名信息.
     */
    private String tmDomain;

    /**
     * 事务item.
     */
    private List<TxTransactionItem> itemList;

}
