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

package org.dromara.raincat.manager.service.execute;

import com.google.gson.Gson;
import org.apache.commons.collections.CollectionUtils;
import org.dromara.raincat.common.enums.TransactionStatusEnum;
import org.dromara.raincat.common.holder.LogUtil;
import org.dromara.raincat.common.holder.httpclient.OkHttpTools;
import org.dromara.raincat.common.netty.bean.HeartBeat;
import org.dromara.raincat.common.netty.bean.TxTransactionItem;
import org.dromara.raincat.manager.config.ChannelSender;
import org.dromara.raincat.manager.config.Constant;
import org.dromara.raincat.manager.config.ExecutorMessageTool;
import org.dromara.raincat.manager.service.TxManagerService;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;
import org.springframework.beans.factory.annotation.Autowired;
import org.springframework.stereotype.Component;

import java.io.IOException;
import java.util.List;
import java.util.Map;
import java.util.Objects;
import java.util.concurrent.CompletableFuture;
import java.util.stream.Collectors;

/**
 * TxTransactionExecutorService.
 * @author xiaoyu
 */
@Component
public class TxTransactionExecutorService extends AbstractTxTransactionExecutor {

    private static final Logger LOGGER = LoggerFactory.getLogger(TxTransactionExecutorService.class);

    private static final Gson GSON = new Gson();

    @Autowired
    public TxTransactionExecutorService(final TxManagerService txManagerService) {
        super.setTxManagerService(txManagerService);
    }

    @Override
    protected void doRollBack(final String txGroupId,
                              final List<TxTransactionItem> txTransactionItems,
                              final List<TxTransactionItem> elseItems) {
        try {
            if (CollectionUtils.isNotEmpty(txTransactionItems)) {
                final CompletableFuture[] cfs = txTransactionItems
                        .stream()
                        .map(item ->
                                CompletableFuture.runAsync(() -> {
                                    ChannelSender channelSender = new ChannelSender();
                                    HeartBeat heartBeat = ExecutorMessageTool.buildMessage(item, channelSender,
                                            TransactionStatusEnum.ROLLBACK);
                                    if (Objects.nonNull(channelSender.getChannel())) {
                                        channelSender.getChannel().writeAndFlush(heartBeat);
                                    } else {
                                        LOGGER.error("txManger rollback指令失败，channel为空，事务组id：{}, 事务taskId为:{}",
                                                txGroupId, item.getTaskKey());
                                    }

                                }).whenComplete((v, e) ->
                                        LogUtil.info(LOGGER, "txManger 成功发送rollback指令 事务taskId为：{}", item::getTaskKey)))
                        .toArray(CompletableFuture[]::new);
                CompletableFuture.allOf(cfs).join();
                LogUtil.info(LOGGER, "txManger 成功发送rollback指令 事务组id为：{}", () -> txGroupId);
            }
            httpExecute(elseItems, TransactionStatusEnum.ROLLBACK);
        } catch (Exception e) {
            e.printStackTrace();
            LogUtil.info(LOGGER, "txManger 发送rollback指令异常 ", e::getMessage);
        }
    }

    @Override
    protected void doCommit(final String txGroupId,
                            final List<TxTransactionItem> txTransactionItems,
                            final List<TxTransactionItem> elseItems) {
        try {
            txTransactionItems.forEach(item -> {
                ChannelSender sender = new ChannelSender();
                HeartBeat heartBeat = ExecutorMessageTool.buildMessage(item, sender, TransactionStatusEnum.COMMIT);
                if (Objects.nonNull(sender.getChannel())) {
                    sender.getChannel().writeAndFlush(heartBeat);
                    LogUtil.info(LOGGER, "txManger 成功发送doCommit指令 事务taskId为：{}", item::getTaskKey);
                } else {
                    LOGGER.error("txManger 发送doCommit指令失败，channel为空，事务组id：{}, 事务taskId为:{}", txGroupId, item.getTaskKey());
                }

            });
            httpExecute(elseItems, TransactionStatusEnum.COMMIT);
        } catch (Exception e) {
            e.printStackTrace();
            LogUtil.info(LOGGER, "txManger 发送doCommit指令异常 ", e::getMessage);
        }

    }

    /**
     * 获取当前连接的channel  为什么？
     * 因为如果tm是集群环境，可能业务的channel对象连接到不同的tm
     * 那么当前的tm可没有其他业务模块的长连接信息，那么就应该做：
     * 1.检查当前tm的channel状态，并只提交当前渠道的命令
     * 2.通知 连接到其他tm的channel，执行命令
     * 通过http 执行 连接到其他tm 的channel.
     *
     * @param elseItems             其他的渠道集合
     * @param transactionStatusEnum 执行动作
     */
    private void httpExecute(final List<TxTransactionItem> elseItems,
                             final TransactionStatusEnum transactionStatusEnum) {
        if (CollectionUtils.isNotEmpty(elseItems)) {
            //按照域名进行分组
            final Map<String, List<TxTransactionItem>> senderItems =
                    elseItems.stream().collect(Collectors.groupingBy(TxTransactionItem::getTmDomain));
            senderItems.forEach((k, v) -> {
                try {
                    if (transactionStatusEnum.getCode() == TransactionStatusEnum.COMMIT.getCode()) {
                        OkHttpTools.getInstance().post(String.format(Constant.HTTP_COMMIT, k), GSON.toJson(v));
                    } else if (transactionStatusEnum.getCode() == TransactionStatusEnum.ROLLBACK.getCode()) {
                        OkHttpTools.getInstance().post(String.format(Constant.HTTP_ROLLBACK, k), GSON.toJson(v));
                    }
                } catch (IOException e) {
                    e.printStackTrace();
                }
            });

        }
    }

}
