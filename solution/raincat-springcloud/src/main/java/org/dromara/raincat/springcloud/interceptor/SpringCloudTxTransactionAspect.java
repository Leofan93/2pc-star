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

package org.dromara.raincat.springcloud.interceptor;

import org.aspectj.lang.annotation.Aspect;
import org.dromara.raincat.core.interceptor.AbstractTxTransactionAspect;
import org.springframework.beans.factory.annotation.Autowired;
import org.springframework.core.Ordered;
import org.springframework.stereotype.Component;

/**
 * SpringCloudTxTransactionAspect.
 *
 * @author xiaoyu
 */
@Aspect
@Component
public class SpringCloudTxTransactionAspect extends AbstractTxTransactionAspect implements Ordered {


    /**
     * Instantiates a new Spring cloud tx transaction aspect.
     *
     * @param springCloudTxTransactionInterceptor the spring cloud tx transaction interceptor
     */
    @Autowired
    public SpringCloudTxTransactionAspect(final SpringCloudTxTransactionInterceptor springCloudTxTransactionInterceptor) {
        this.setTxTransactionInterceptor(springCloudTxTransactionInterceptor);
    }

    @Override
    public int getOrder() {
        return Ordered.HIGHEST_PRECEDENCE;
    }
}
